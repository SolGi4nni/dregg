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
//! This module is the STAGED Rust shadow of that in-AIR forcing. The first half is the three degree-≤2
//! selector-forcing gates ([`gentian_selector_forcing_gates`]); the second half (OPTION B REALIZED,
//! below) DISCHARGES the two hypotheses the first GENTIAN rung left modeled — the recompute is a
//! felt-domain chip lookup ([`gentian_recompute_lookup`]) and the decode is an in-AIR is-zero + OR-fold
//! gadget ([`gentian_decode_gates`]). The Lean soundness rung proving the selector forcing holds under
//! ONLY the two CR floors (`ChipTableSound` + `FloorDigestBinds`, no off-band `hverifier`) is
//! `Dregg2.Deos.InAirAuthorityDigestGadget` (`gentian_selector_forced_discharged` /
//! `gentian_settle_forced_discharged`); the under-hypothesis predecessor is
//! `Dregg2.Deos.InAirAuthorityDigestSelector`.
//!
//! ## STAGED — built BESIDE the deployed, NOT flipped, NOT yet in a committed VK
//!
//! These constraints are NOT emitted into a committed welded descriptor / VK and NOT routed onto any
//! live path. The deployed descriptors / VK are byte-identical. What remains to the FLIP
//! (`IN-AIR-AUTHORITY-DIGEST-GADGET.md` §7): EMIT the gadget descriptor into a staged registry (the
//! Option-B reinterpretation of the committed `B_AUTHORITY_DIGEST` limb as the felt-domain floor digest,
//! the flag-day VK bytes) + a satisfying STARK PRODUCER (extend `generate_rotated_settle_escrow_trace`
//! to fill the floor / is-zero-witness / lane columns + the chip rows, then a full prove/verify) +
//! committing the VK + live admission. This module carries the gates + the producer's decode-witness +
//! gate-eval teeth; the STARK producer is the named next rung.
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

use super::pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW;
use super::satisfaction_weld::ESCROW_SEL_COL;
use super::trace_rotated::{B_AUTHORITY_DIGEST, BEFORE_BASE};
use crate::descriptor_ir2::{CHIP_RATE, LookupSpec, TID_P2, VmConstraint2};
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

// ============================================================================
// OPTION B REALIZED — the in-AIR required-floor decode + felt-domain recompute that DISCHARGE the
// named-modeled `hrecompute` / `hdecode` (Lean `Dregg2.Deos.InAirAuthorityDigestGadget`, STAGED).
//
// The first GENTIAN rung left two hypotheses standing for the recompute/decode gadget faithfulness.
// This realizes them: the recompute is a felt-domain chip lookup (`gentian_recompute_lookup`,
// discharged by `chip_lookup_sound` against the deployed chip table), and the decode is the in-AIR
// is-zero + OR-fold gadget below (discharged by pure field arithmetic). After this, the selector
// forcing holds under ONLY the two CR floors (`ChipTableSound` + `FloorDigestBinds`) — no off-band
// verifier discipline. STAGED: not in a committed VK, no live routing, deployed VK byte-identical.
// ============================================================================

/// The fixed floor arity (≤ `CHIP_RATE`): the representative declared-caveat slot count. (The chip
/// lookup is fixed-arity, so generalizing the slot count repeats the same per-slot is-zero gadget;
/// the Lean `isZero_from_gates` is reused verbatim.)
pub const FLOOR_ARITY: usize = 2;

/// The escrow tag as a felt-domain constant (the matched required tag the decode looks for).
const TAG_ESCROW: i64 = SLOT_CAVEAT_TAG_SETTLE_ESCROW as i64;

/// Witnessed floor slot `k` column (`PARAM_BASE + 5 + k`). Lean twin `FLOOR0_COL`/`FLOOR1_COL`.
pub const fn floor_slot_col(k: usize) -> usize {
    super::columns::PARAM_BASE + 5 + k
}

/// is-zero boolean column for floor slot `k` (`PARAM_BASE + 7 + k`). Lean twin `B0_COL`/`B1_COL`.
pub const fn floor_bit_col(k: usize) -> usize {
    super::columns::PARAM_BASE + 7 + k
}

/// inverse-witness column for floor slot `k` (`PARAM_BASE + 9 + k`). Lean twin `INV0_COL`/`INV1_COL`.
pub const fn floor_inv_col(k: usize) -> usize {
    super::columns::PARAM_BASE + 9 + k
}

/// The 7 exposed permutation lane columns (`CHIP_OUT_LANES - 1`), `PARAM_BASE + 11 .. + 17`. Lean
/// twin `laneCols`.
fn lane_cols() -> Vec<usize> {
    (0..7)
        .map(|j| super::columns::PARAM_BASE + 11 + j)
        .collect()
}

/// One is-zero **defining** gate `b_k + (F_k − 17)·inv_k − 1 == 0` (so `b_k = 1 − (F_k−17)·inv_k`).
/// Lean twin `isZeroDefGate`.
fn is_zero_def_gate(floor_col: usize, bool_col: usize, inv_col: usize) -> VmConstraint2 {
    let body = LeanExpr::add(
        LeanExpr::add(
            LeanExpr::var(bool_col),
            LeanExpr::mul(
                LeanExpr::add(LeanExpr::var(floor_col), LeanExpr::constant(-TAG_ESCROW)),
                LeanExpr::var(inv_col),
            ),
        ),
        LeanExpr::constant(-1),
    );
    VmConstraint2::Base(VmConstraint::Gate(body))
}

/// One is-zero **forcing** gate `(F_k − 17)·b_k == 0` (over the field, forces `b_k = 0` when
/// `F_k ≠ 17`). Lean twin `isZeroForceGate`.
fn is_zero_force_gate(floor_col: usize, bool_col: usize) -> VmConstraint2 {
    let body = LeanExpr::mul(
        LeanExpr::add(LeanExpr::var(floor_col), LeanExpr::constant(-TAG_ESCROW)),
        LeanExpr::var(bool_col),
    );
    VmConstraint2::Base(VmConstraint::Gate(body))
}

/// The OR-fold gate `FLOOR_ESCROW_COL − (b0 + b1 − b0·b1) == 0` (the boolean OR of the two slot
/// bits). Lean twin `decodeOrGate`.
fn decode_or_gate() -> VmConstraint2 {
    let b0 = LeanExpr::var(floor_bit_col(0));
    let b1 = LeanExpr::var(floor_bit_col(1));
    let or = LeanExpr::add(
        LeanExpr::add(b0.clone(), b1.clone()),
        LeanExpr::mul(LeanExpr::constant(-1), LeanExpr::mul(b0, b1)),
    );
    let body = LeanExpr::add(
        LeanExpr::var(FLOOR_ESCROW_COL),
        LeanExpr::mul(LeanExpr::constant(-1), or),
    );
    VmConstraint2::Base(VmConstraint::Gate(body))
}

/// **THE IN-AIR DECODE GADGET (STAGED).** The five `VmConstraint::Gate` constraints that DISCHARGE
/// `hdecode`: per-slot is-zero (defining + forcing) gates that force `b_k = (F_k == 17)`, then an
/// OR-fold that forces `FLOOR_ESCROW_COL = (escrow ∈ floor)`. So the floor column IS the decoded
/// required-tag floor by construction — pure field arithmetic, NO crypto floor. Rust shadow of the
/// Lean `decodeGates`.
pub fn gentian_decode_gates() -> Vec<VmConstraint2> {
    vec![
        is_zero_def_gate(floor_slot_col(0), floor_bit_col(0), floor_inv_col(0)),
        is_zero_force_gate(floor_slot_col(0), floor_bit_col(0)),
        is_zero_def_gate(floor_slot_col(1), floor_bit_col(1), floor_inv_col(1)),
        is_zero_force_gate(floor_slot_col(1), floor_bit_col(1)),
        decode_or_gate(),
    ]
}

/// **THE RECOMPUTE CHIP LOOKUP (STAGED).** A poseidon2 chip lookup whose digest column is
/// `WIT_DIGEST_COL` and whose inputs are the witnessed floor columns. Against the deployed sound
/// chip table the lever (Lean `chip_lookup_sound`) forces `WIT_DIGEST_COL = hash_many(floor)`,
/// DISCHARGING `hrecompute`: the witnessed-digest column carries the felt-domain digest of the
/// witnessed floor. The recompute-bind gate then ties it to the committed `B_AUTHORITY_DIGEST` limb
/// (read, under Option B, as that same felt-domain floor digest). Rust shadow of the Lean
/// `gentianRecomputeLookup`.
pub fn gentian_recompute_lookup() -> VmConstraint2 {
    let mut tuple: Vec<LeanExpr> = Vec::with_capacity(CHIP_RATE + 1 + 8);
    // arity tag.
    tuple.push(LeanExpr::constant(FLOOR_ARITY as i64));
    // CHIP_RATE inputs: the floor slots, zero-padded.
    for k in 0..CHIP_RATE {
        if k < FLOOR_ARITY {
            tuple.push(LeanExpr::var(floor_slot_col(k)));
        } else {
            tuple.push(LeanExpr::constant(0));
        }
    }
    // the digest column (out0) + the 7 exposed lanes.
    tuple.push(LeanExpr::var(WIT_DIGEST_COL));
    for c in lane_cols() {
        tuple.push(LeanExpr::var(c));
    }
    VmConstraint2::Lookup(LookupSpec {
        table: TID_P2,
        tuple,
    })
}

/// **THE FULL GENTIAN GADGET CONSTRAINTS (STAGED).** The three selector-forcing gates +
/// the realized recompute chip lookup + the in-AIR decode gates — the Rust shadow of the Lean
/// `gentianGadgetDescriptor`'s appended block (`gentianRecomputeLookup :: decodeGates` plus the
/// reused `gentianGates`). A satisfying proof on a declared-escrow cell forces `ESCROW_SEL_COL = 1`
/// under only the chip-table + felt-hash CR floors — no `hrecompute`/`hdecode`.
pub fn gentian_gadget_constraints() -> Vec<VmConstraint2> {
    let mut cs = gentian_selector_forcing_gates();
    cs.push(gentian_recompute_lookup());
    cs.extend(gentian_decode_gates());
    cs
}

/// A producer's witnessed-floor assignment for the gadget columns: for each of the two slots the
/// is-zero boolean `b_k = (F_k == 17)` and its inverse witness (`(F_k − 17)⁻¹`, or 0 when zero), plus
/// the OR-folded `FLOOR_ESCROW_COL` bit. This is the EXACT assignment that satisfies
/// [`gentian_decode_gates`] for the witnessed floor — the decode half of the gadget producer.
#[derive(Clone, Copy, Debug)]
pub struct GentianDecodeWitness {
    /// The per-slot is-zero booleans.
    pub bits: [u32; FLOOR_ARITY],
    /// The per-slot inverse witnesses.
    pub invs: [crate::field::BabyBear; FLOOR_ARITY],
    /// The OR-folded escrow-presence bit (`FLOOR_ESCROW_COL`).
    pub floor_escrow: u32,
}

/// Compute the satisfying decode witness for a witnessed required-tag floor (the producer half that
/// discharges `hdecode` at trace-build time). `b_k = 1` iff slot `k` is the escrow tag; `inv_k` is
/// the field inverse of `F_k − 17` (0 when zero); `floor_escrow = OR(b0, b1)`.
pub fn gentian_decode_witness(floor: [u32; FLOOR_ARITY]) -> GentianDecodeWitness {
    use crate::field::BabyBear;
    let tag = BabyBear::new(SLOT_CAVEAT_TAG_SETTLE_ESCROW);
    let mut bits = [0u32; FLOOR_ARITY];
    let mut invs = [BabyBear::ZERO; FLOOR_ARITY];
    for k in 0..FLOOR_ARITY {
        let d = BabyBear::new(floor[k]) - tag;
        if d == BabyBear::ZERO {
            bits[k] = 1;
            invs[k] = BabyBear::ZERO;
        } else {
            bits[k] = 0;
            invs[k] = d.inverse().expect("nonzero field element is invertible");
        }
    }
    let floor_escrow = bits[0] | bits[1];
    GentianDecodeWitness {
        bits,
        invs,
        floor_escrow,
    }
}

#[cfg(test)]
mod gadget_tests {
    use super::*;
    use crate::descriptor_ir2::eval_lean_expr;
    use crate::field::BabyBear;
    use crate::poseidon2::hash_many;

    fn gate_body(c: &VmConstraint2) -> &LeanExpr {
        match c {
            VmConstraint2::Base(VmConstraint::Gate(body)) => body,
            _ => panic!("expected a Gate constraint"),
        }
    }

    /// Build a satisfying gadget row for an honest declared-escrow turn over the witnessed `floor`,
    /// with the selector set to `sel`. Fills the floor slots, the is-zero witness, the OR bit, the
    /// committed limb + recompute output as the felt-domain floor digest (the recompute-bind tie).
    fn make_gadget_row(floor: [u32; FLOOR_ARITY], sel: u32) -> Vec<BabyBear> {
        let width = auth_digest_col()
            .max(WIT_DIGEST_COL)
            .max(FLOOR_ESCROW_COL)
            .max(floor_slot_col(FLOOR_ARITY - 1))
            .max(floor_bit_col(FLOOR_ARITY - 1))
            .max(floor_inv_col(FLOOR_ARITY - 1))
            .max(ESCROW_SEL_COL)
            + 1;
        let mut row = vec![BabyBear::ZERO; width];
        let w = gentian_decode_witness(floor);
        // the felt-domain floor digest: the recompute output AND the committed limb (Option B).
        let floor_felts: Vec<BabyBear> = floor.iter().map(|&t| BabyBear::new(t)).collect();
        let digest = hash_many(&floor_felts);
        row[WIT_DIGEST_COL] = digest;
        row[auth_digest_col()] = digest;
        for k in 0..FLOOR_ARITY {
            row[floor_slot_col(k)] = BabyBear::new(floor[k]);
            row[floor_bit_col(k)] = BabyBear::new(w.bits[k]);
            row[floor_inv_col(k)] = w.invs[k];
        }
        row[FLOOR_ESCROW_COL] = BabyBear::new(w.floor_escrow);
        row[ESCROW_SEL_COL] = BabyBear::new(sel);
        row
    }

    /// The selector-forcing + decode gates (the recompute lookup is exercised separately — its
    /// soundness is the chip-table lever, tested in the chip machinery).
    fn gadget_gates() -> Vec<VmConstraint2> {
        let mut g = gentian_selector_forcing_gates();
        g.extend(gentian_decode_gates());
        g
    }

    fn all_gates_zero(gates: &[VmConstraint2], row: &[BabyBear]) -> bool {
        gates
            .iter()
            .all(|g| eval_lean_expr(gate_body(g), row) == BabyBear::ZERO)
    }

    #[test]
    fn columns_are_distinct() {
        let cols = [
            WIT_DIGEST_COL,
            FLOOR_ESCROW_COL,
            auth_digest_col(),
            ESCROW_SEL_COL,
            floor_slot_col(0),
            floor_slot_col(1),
            floor_bit_col(0),
            floor_bit_col(1),
            floor_inv_col(0),
            floor_inv_col(1),
        ];
        for i in 0..cols.len() {
            for j in (i + 1)..cols.len() {
                assert_ne!(cols[i], cols[j], "gadget columns must be distinct");
            }
        }
    }

    #[test]
    fn honest_declared_escrow_decodes_and_forces_selector() {
        // A floor that DECLARES escrow (slot 0 = tag 17, slot 1 = some other tag): the is-zero
        // gadget decodes FLOOR_ESCROW = 1, the selector-force gate then DEMANDS the selector. With a
        // recomputed digest (WIT = AUTH) and the selector ON, EVERY gadget gate vanishes.
        let gates = gadget_gates();
        let floor = [SLOT_CAVEAT_TAG_SETTLE_ESCROW, 19];
        let row = make_gadget_row(floor, /*sel*/ 1);
        assert_eq!(
            row[FLOOR_ESCROW_COL],
            BabyBear::ONE,
            "an escrow-declaring floor decodes FLOOR_ESCROW = 1 — hdecode DISCHARGED"
        );
        assert!(
            all_gates_zero(&gates, &row),
            "honest declared-escrow (decoded floor, recomputed digest, selector on) satisfies every \
             gadget gate"
        );
    }

    #[test]
    fn declared_escrow_with_selector_off_is_unsat() {
        // THE KEY TOOTH: a declared-escrow floor (decodes to 1) whose forger dodges by SEL = 0
        // violates the selector-force gate — the selector cannot be turned off IN-AIR, no off-band
        // demand needed.
        let gates = gadget_gates();
        let row = make_gadget_row([SLOT_CAVEAT_TAG_SETTLE_ESCROW, 19], /*sel*/ 0);
        assert!(
            !all_gates_zero(&gates, &row),
            "declared-escrow floor with selector 0 must violate the selector-force gate"
        );
    }

    #[test]
    fn non_escrow_floor_leaves_selector_free() {
        // A floor declaring NO escrow decodes FLOOR_ESCROW = 0; the selector-force gate is inert, so
        // the gadget never falsely demands the weld off a non-capacity turn. Both SEL = 0/1 satisfy.
        let gates = gadget_gates();
        let off = make_gadget_row([6, 19], /*sel*/ 0);
        let on = make_gadget_row([6, 19], /*sel*/ 1);
        assert_eq!(off[FLOOR_ESCROW_COL], BabyBear::ZERO, "no escrow ⟹ floor 0");
        assert!(
            all_gates_zero(&gates, &off) && all_gates_zero(&gates, &on),
            "a non-escrow floor leaves the selector free — no false demand"
        );
    }

    #[test]
    fn forged_decode_bit_is_unsat() {
        // A forger who keeps an escrow floor but flips the decoded bit to 0 (to make the
        // selector-force gate vacuous) breaks the OR-fold / is-zero gates — the decode cannot lie.
        let mut row = make_gadget_row([SLOT_CAVEAT_TAG_SETTLE_ESCROW, 19], /*sel*/ 0);
        row[FLOOR_ESCROW_COL] = BabyBear::ZERO; // lie: claim no escrow
        assert!(
            !all_gates_zero(&gadget_gates(), &row),
            "forging FLOOR_ESCROW = 0 on an escrow floor must violate the OR-fold gate"
        );
    }

    #[test]
    fn forged_is_zero_bit_is_unsat() {
        // A forger who sets a slot's is-zero bit to 0 despite the slot BEING the escrow tag breaks
        // the is-zero DEFINING gate (b + (F-17)·inv - 1 == 0 with F=17 forces b=1).
        let mut row = make_gadget_row([SLOT_CAVEAT_TAG_SETTLE_ESCROW, 19], /*sel*/ 1);
        row[floor_bit_col(0)] = BabyBear::ZERO;
        row[floor_inv_col(0)] = BabyBear::ZERO;
        assert!(
            !all_gates_zero(&gadget_gates(), &row),
            "forging b0 = 0 with F0 = escrow must violate the is-zero defining gate"
        );
    }

    #[test]
    fn forged_recompute_digest_is_unsat() {
        // A producer whose recompute output (WIT) does NOT equal the committed limb (AUTH) violates
        // the recompute-bind gate (under CR, the alternate-floor dodge being caught).
        let mut row = make_gadget_row([SLOT_CAVEAT_TAG_SETTLE_ESCROW, 19], /*sel*/ 1);
        row[WIT_DIGEST_COL] = row[WIT_DIGEST_COL] + BabyBear::ONE; // mismatch the committed limb
        assert!(
            !all_gates_zero(&gadget_gates(), &row),
            "a recompute output != the committed authority-digest limb must violate the bind gate"
        );
    }

    #[test]
    fn recompute_lookup_tuple_is_chip_shaped() {
        // The recompute lookup targets the poseidon2 chip table and has the chip tuple arity
        // (1 arity + CHIP_RATE inputs + 8 output lanes), with the floor slots as the live inputs and
        // WIT_DIGEST_COL as the digest column (out0).
        let lookup = gentian_recompute_lookup();
        match lookup {
            VmConstraint2::Lookup(spec) => {
                assert_eq!(spec.table, TID_P2, "targets the poseidon2 chip table");
                assert_eq!(
                    spec.tuple.len(),
                    1 + CHIP_RATE + 8,
                    "chip tuple arity (arity + CHIP_RATE inputs + 8 lanes)"
                );
                assert_eq!(
                    spec.tuple[0],
                    LeanExpr::constant(FLOOR_ARITY as i64),
                    "arity tag = floor arity"
                );
                assert_eq!(
                    spec.tuple[1],
                    LeanExpr::var(floor_slot_col(0)),
                    "first input is floor slot 0"
                );
                assert_eq!(
                    spec.tuple[1 + CHIP_RATE],
                    LeanExpr::var(WIT_DIGEST_COL),
                    "the digest column (out0) is WIT_DIGEST_COL"
                );
            }
            _ => panic!("expected a Lookup constraint"),
        }
    }
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
