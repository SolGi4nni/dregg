//! # `authority_digest_weld` — the GENTIAN KEYSTONE: the in-AIR authority-digest → selector forcing
//! gadget (the TERMINAL blocker of the sealed-escrow VK flip, STAGED).
//!
//! `docs/deos/IN-AIR-AUTHORITY-DIGEST-GADGET.md` is the design.
//! `docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md` §6 item 2 names the last soundness gap before the
//! escrow weld can flip to a deployed PURE-LIGHT-CLIENT truth:
//!
//! The four satisfaction gates (`satisfaction_weld::settle_escrow_satisfaction_gates`) are
//! SELECTOR-GATED — they bite only when the capacity selector `ESCROW_SEL_COL` is `1`. A forger
//! settling a half-open escrow dodges them by setting the selector `0` — UNLESS the selector is FORCED
//! on for any cell whose COMMITTED declaration requires the escrow capacity. For a verifier holding the
//! committed-state opening, the deployed COVERAGE carrier supplies the demand. For a PURE light client
//! (commitments only), the forcing must be done IN-AIR — it holds the committed authority-digest limb
//! (r23, wide-bound), NOT the declaration preimage.
//!
//! This module is the STAGED Rust shadow of that in-AIR forcing: the three degree-≤2 gates that bind
//! the selector to the committed authority digest. The Lean soundness rung proving these gates FORCE
//! the selector from the committed declaration (under the `DeclCommitBinds` collision-resistance floor)
//! is `Dregg2.Deos.InAirAuthorityDigestSelector` (`gentian_selector_forced` / `gentian_settle_forced`).
//!
//! ## STAGED — built BESIDE the deployed, NOT flipped, NOT yet in a committed VK
//!
//! These constraints are NOT emitted into a committed welded descriptor / VK and NOT routed onto any
//! live path. The deployed descriptors / VK are byte-identical. What remains (the genuinely-VK-affecting
//! tail, `IN-AIR-AUTHORITY-DIGEST-GADGET.md` §4): the LITERAL in-AIR recompute of
//! `cell::commitment::compute_authority_digest_felt` (a `hash_bytes` sponge over the witnessed,
//! variable-length postcard declaration — needs either a new byte-sponge constraint variant, Option A,
//! or a felt-domain required-floor limb + chip-lookup recompute, Option B), and the in-AIR
//! `required_capacity_caveat_tags` decode that fills `FLOOR_ESCROW_COL`. This module builds the EQUALITY
//! SKELETON (recompute-bind + decode-boolean + selector-force); the recompute/decode chains are the
//! named remaining work.
//!
//! ## The constraint shape (the three GENTIAN gates)
//!
//!  1. **recompute-bind** `WIT_DIGEST_COL − AUTH_DIGEST_COL == 0` — the in-AIR recompute output equals
//!     the committed `B_AUTHORITY_DIGEST` limb (wide-bound). Under collision-resistance this forces the
//!     witnessed declaration to the committed one's required-tag floor.
//!  2. **decode-boolean** `FLOOR_ESCROW_COL · (FLOOR_ESCROW_COL − 1) == 0` — the decoded floor bit is
//!     a boolean.
//!  3. **selector-force** `FLOOR_ESCROW_COL · (ESCROW_SEL_COL − 1) == 0` — when the floor includes
//!     escrow, the selector is forced ON; inert otherwise.

use super::satisfaction_weld::ESCROW_SEL_COL;
use super::trace_rotated::{B_AUTHORITY_DIGEST, BEFORE_BASE};
use crate::descriptor_ir2::VmConstraint2;
use crate::lean_descriptor_air::{LeanExpr, VmConstraint};

/// **THE RECOMPUTE-OUTPUT COLUMN** — a free PARAM slot (`param3 = PARAM_BASE + 3 = 71`) the producer
/// fills with the in-AIR `hash_bytes` recompute of the witnessed declaration's authority digest. The
/// recompute-bind gate ties it to the committed limb. Lean twin
/// `Dregg2.Deos.InAirAuthorityDigestSelector.GENTIAN_WIT_DIGEST_COL`.
pub const WIT_DIGEST_COL: usize = super::columns::PARAM_BASE + 3;

/// **THE DECODED-FLOOR COLUMN** — a free PARAM slot (`param4 = PARAM_BASE + 4 = 72`) the producer fills
/// with the boolean "the witnessed declaration's required-tag floor includes the escrow tag". Lean twin
/// `GENTIAN_FLOOR_ESCROW_COL`.
pub const FLOOR_ESCROW_COL: usize = super::columns::PARAM_BASE + 4;

/// **THE COMMITTED AUTHORITY-DIGEST COLUMN** — the rotated `B_AUTHORITY_DIGEST` limb (r23, limb 24) of
/// the BEFORE block, which the chained `wireCommitR` → ~124-bit wide commit absorbs (so a pure light
/// client binds it). The recompute-bind gate constrains the recompute output equal to this column.
/// Lean twin `gentianAuthDigestCol = EFFECT_VM_WIDTH + 24`.
pub const fn auth_digest_col() -> usize {
    BEFORE_BASE + B_AUTHORITY_DIGEST
}

/// One degree-1 difference gate `(a − b) == 0` as a `VmConstraint::Gate` body.
fn diff_gate(a: usize, b: usize) -> VmConstraint2 {
    let body = LeanExpr::add(
        LeanExpr::var(a),
        LeanExpr::mul(LeanExpr::constant(-1), LeanExpr::var(b)),
    );
    VmConstraint2::Base(VmConstraint::Gate(body))
}

/// One degree-2 product gate `col · (other − 1) == 0` as a `VmConstraint::Gate` body. With `col = 1`
/// this forces `other = 1`; with `col = 0` it is inert.
fn product_minus_one_gate(col: usize, other: usize) -> VmConstraint2 {
    let body = LeanExpr::mul(
        LeanExpr::var(col),
        LeanExpr::add(LeanExpr::var(other), LeanExpr::constant(-1)),
    );
    VmConstraint2::Base(VmConstraint::Gate(body))
}

/// **THE GENTIAN IN-AIR SELECTOR-FORCING GATES (STAGED).** The three `VmConstraint::Gate` constraints
/// that force the capacity selector ON from the committed authority digest:
///
///  1. `WIT_DIGEST_COL − AUTH_DIGEST_COL == 0` (recompute-bind)
///  2. `FLOOR_ESCROW_COL · (FLOOR_ESCROW_COL − 1) == 0` (decode-boolean)
///  3. `FLOOR_ESCROW_COL · (ESCROW_SEL_COL − 1) == 0` (selector-force)
///
/// The Rust shadow of the Lean `gentianGates`; a satisfying proof on a declared-escrow cell (its
/// committed authority digest requires the escrow tag, so the decode fills `FLOOR_ESCROW_COL = 1`)
/// FORCES `ESCROW_SEL_COL = 1`, lighting the satisfaction weld — un-dodgeably, for a pure light client.
/// STAGED: not yet in a committed VK; the recompute/decode chains that fill the witnessed columns are
/// the named remaining work.
pub fn gentian_selector_forcing_gates() -> Vec<VmConstraint2> {
    vec![
        diff_gate(WIT_DIGEST_COL, auth_digest_col()),
        product_minus_one_gate(FLOOR_ESCROW_COL, FLOOR_ESCROW_COL),
        product_minus_one_gate(FLOOR_ESCROW_COL, ESCROW_SEL_COL),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_ir2::eval_lean_expr;
    use crate::field::BabyBear;

    fn gate_body(c: &VmConstraint2) -> &LeanExpr {
        match c {
            VmConstraint2::Base(VmConstraint::Gate(body)) => body,
            _ => panic!("expected a Gate constraint"),
        }
    }

    /// A wide-enough zero row with the four gentian-relevant columns set.
    fn make_row(wit: u32, auth: u32, floor: u32, sel: u32) -> Vec<BabyBear> {
        let width = auth_digest_col()
            .max(WIT_DIGEST_COL)
            .max(FLOOR_ESCROW_COL)
            .max(ESCROW_SEL_COL)
            + 1;
        let mut row = vec![BabyBear::ZERO; width];
        row[WIT_DIGEST_COL] = BabyBear::new(wit);
        row[auth_digest_col()] = BabyBear::new(auth);
        row[FLOOR_ESCROW_COL] = BabyBear::new(floor);
        row[ESCROW_SEL_COL] = BabyBear::new(sel);
        row
    }

    fn all_gates_zero(gates: &[VmConstraint2], row: &[BabyBear]) -> bool {
        gates
            .iter()
            .all(|g| eval_lean_expr(gate_body(g), row) == BabyBear::ZERO)
    }

    #[test]
    fn the_three_distinct_columns() {
        // The two free param slots, the committed limb, and the selector are all distinct, so the
        // gadget does not alias any column.
        assert_eq!(WIT_DIGEST_COL, super::super::columns::PARAM_BASE + 3);
        assert_eq!(FLOOR_ESCROW_COL, super::super::columns::PARAM_BASE + 4);
        assert_eq!(auth_digest_col(), BEFORE_BASE + B_AUTHORITY_DIGEST);
        let cols = [
            WIT_DIGEST_COL,
            FLOOR_ESCROW_COL,
            auth_digest_col(),
            ESCROW_SEL_COL,
        ];
        for i in 0..cols.len() {
            for j in (i + 1)..cols.len() {
                assert_ne!(cols[i], cols[j], "gentian columns must be distinct");
            }
        }
    }

    #[test]
    fn honest_declared_escrow_forces_selector_on() {
        // The committed authority digest requires escrow ⟹ the decode fills FLOOR = 1; a producer that
        // recomputes the digest (WIT = AUTH) and lights the selector (SEL = 1) satisfies every gate.
        let gates = gentian_selector_forcing_gates();
        let row = make_row(
            /*wit*/ 12345, /*auth*/ 12345, /*floor*/ 1, /*sel*/ 1,
        );
        assert!(
            all_gates_zero(&gates, &row),
            "an honest declared-escrow row (digest recomputed, floor decoded, selector on) satisfies \
             every gentian gate"
        );
    }

    #[test]
    fn floor_one_with_selector_off_is_unsat() {
        // THE KEY TOOTH: a declared-escrow cell (floor decodes to 1) whose forger tries to dodge by
        // SEL = 0 violates the selector-force gate. The selector cannot be turned off.
        let gates = gentian_selector_forcing_gates();
        let row = make_row(12345, 12345, /*floor*/ 1, /*sel*/ 0);
        assert!(
            !all_gates_zero(&gates, &row),
            "floor = 1 (escrow declared) with selector 0 must violate the selector-force gate"
        );
    }

    #[test]
    fn forged_digest_is_unsat() {
        // A producer presenting a witnessed declaration whose recomputed digest does NOT match the
        // committed authority-digest limb violates the recompute-bind gate (under CR this is the
        // alternate-declaration dodge being caught).
        let gates = gentian_selector_forcing_gates();
        let row = make_row(/*wit*/ 999, /*auth*/ 12345, 1, 1);
        assert!(
            !all_gates_zero(&gates, &row),
            "a recompute output != the committed authority-digest limb must violate the bind gate"
        );
    }

    #[test]
    fn non_boolean_floor_is_unsat() {
        // The decode-boolean gate forbids a floor column outside {0,1} (a forger cannot set FLOOR to a
        // value that makes the selector-force gate vacuous).
        let gates = gentian_selector_forcing_gates();
        let row = make_row(12345, 12345, /*floor*/ 2, /*sel*/ 1);
        assert!(
            !all_gates_zero(&gates, &row),
            "a non-boolean floor column must violate the decode-boolean gate"
        );
    }

    #[test]
    fn non_escrow_cell_leaves_selector_free() {
        // A cell NOT declaring the escrow capacity decodes FLOOR = 0; the selector-force gate is then
        // inert (selector free), so the gentian gadget never falsely demands the weld off a
        // non-capacity turn. Both SEL = 0 and SEL = 1 satisfy when FLOOR = 0.
        let gates = gentian_selector_forcing_gates();
        let off = make_row(7, 7, /*floor*/ 0, /*sel*/ 0);
        let on = make_row(7, 7, /*floor*/ 0, /*sel*/ 1);
        assert!(
            all_gates_zero(&gates, &off) && all_gates_zero(&gates, &on),
            "with floor = 0 (no escrow declared) the selector is free — no false demand"
        );
    }
}
