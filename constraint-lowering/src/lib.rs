//! # constraint-lowering — the crown-lowering range gadget
//!
//! The reusable inequality primitive that `ConstraintExpr` lacks. The circuit DSL
//! (`dregg_circuit::dsl::ConstraintExpr`) has `Equality / Multiplication / Binary /
//! PiBinding / Transition / Polynomial / Gated` — but **no comparison op**. So the
//! ordering executor teeth (`StateConstraint::FieldGte / FieldLte / Monotonic /
//! StrictMonotonic`) can only reach the proof crown by hand-authoring a
//! bit-decomposition per rule. This crate makes that gadget reusable, so a
//! `StateConstraint → ConstraintExpr` compiler lowers *any* ordering tooth by
//! calling one function.
//!
//! ## The primitive: `a ≥ b` over BabyBear by range-checking the difference
//!
//! Let `d = a − b`. Prove `d ∈ [0, 2^bits)` by bit-decomposition:
//! * `Polynomial`: `a − b − d = 0`  (define the difference column),
//! * `Binary` per bit `b_i`,
//! * `Polynomial`: `Σ 2^i·b_i − d = 0`  (reconstruct `d` from `bits` bits).
//!
//! **Soundness:** if `a ≥ b` and `a − b < 2^bits`, `d` is small and representable.
//! If `a < b`, `d = a − b + p` is huge (~2³¹) and no `bits`-bit decomposition equals
//! it, so the reconstruction is unsatisfiable. Thus the gadget is sound **as long as
//! `bits` bounds the honest domain** (HP, scene index, budget — all small) and
//! `bits < 31` (BabyBear is ~2³¹). Emission is pure `ConstraintExpr` — no new DSL
//! variant, no prover; the caller wires witness generation for the aux columns.
//!
//! ## Honest scope
//! Same-row comparisons (`FieldGte`/`FieldLte` against a column or a constant) are
//! covered here. **`Monotonic`/`StrictMonotonic` are cross-row** (`next ≥ local`);
//! they need the difference taken across the transition, which is a documented
//! follow-on ([`emit_ge`] over a diff the compiler supplies from a `Transition`).
//! If a native `RangeLookup`/`Lte` `ConstraintExpr` variant is later added for
//! succinctness, this API is unchanged — only the internal lowering swaps.

use dregg_circuit::dsl::{ConstraintExpr, PolyTerm};
use dregg_circuit::field::BabyBear;

/// Hands out fresh auxiliary column indices for the gadget's witness (the diff
/// column + the decomposition bits). The caller wires witness generation to fill
/// them; start it past the circuit's real columns via [`ColAlloc::new`].
pub struct ColAlloc {
    next: usize,
}

impl ColAlloc {
    /// Start allocating aux columns at `first_free` (past the real trace columns).
    pub fn new(first_free: usize) -> Self {
        Self { next: first_free }
    }
    pub fn alloc(&mut self) -> usize {
        let c = self.next;
        self.next += 1;
        c
    }
    pub fn alloc_n(&mut self, n: usize) -> Vec<usize> {
        (0..n).map(|_| self.alloc()).collect()
    }
    /// The next column index that will be handed out (i.e. the current width).
    pub fn next_free(&self) -> usize {
        self.next
    }
}

/// The auxiliary columns a comparison introduces, so the caller can fill the
/// witness: `local[diff]` = the (non-negative) difference, `local[bits[i]]` = its
/// i-th bit.
pub struct CmpAux {
    pub diff: usize,
    pub bits: Vec<usize>,
}

/// Emit constraints proving `expr ≥ 0`, i.e. `expr ∈ [0, 2^bits)`, where `expr` is a
/// linear form over columns (a `Vec<PolyTerm>`; a `PolyTerm` with empty
/// `col_indices` is a constant term). This is the kernel of every comparison.
///
/// Panics if `bits` is not in `1..31` (BabyBear range).
pub fn emit_nonneg(
    expr: Vec<PolyTerm>,
    bits: usize,
    alloc: &mut ColAlloc,
) -> (Vec<ConstraintExpr>, CmpAux) {
    assert!(
        (1..31).contains(&bits),
        "range `bits` must be in 1..31 for BabyBear (~2^31); got {bits}"
    );
    let diff = alloc.alloc();
    let bit_cols = alloc.alloc_n(bits);
    let mut cs = Vec::with_capacity(bits + 2);

    // (1) define the difference column: expr − diff = 0
    let mut define = expr;
    define.push(PolyTerm {
        coeff: -BabyBear::ONE,
        col_indices: vec![diff],
    });
    cs.push(ConstraintExpr::Polynomial { terms: define });

    // (2) each decomposition column is a bit
    for &bc in &bit_cols {
        cs.push(ConstraintExpr::Binary { col: bc });
    }

    // (3) reconstruct: Σ 2^i·bit_i − diff = 0  (forces diff ∈ [0, 2^bits))
    let mut recon: Vec<PolyTerm> = bit_cols
        .iter()
        .enumerate()
        .map(|(i, &bc)| PolyTerm {
            coeff: BabyBear::new(1u32 << i),
            col_indices: vec![bc],
        })
        .collect();
    recon.push(PolyTerm {
        coeff: -BabyBear::ONE,
        col_indices: vec![diff],
    });
    cs.push(ConstraintExpr::Polynomial { terms: recon });

    (
        cs,
        CmpAux {
            diff,
            bits: bit_cols,
        },
    )
}

/// `local[a] ≥ local[b]`.
pub fn emit_ge(
    a: usize,
    b: usize,
    bits: usize,
    alloc: &mut ColAlloc,
) -> (Vec<ConstraintExpr>, CmpAux) {
    emit_nonneg(
        vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![a],
            },
            PolyTerm {
                coeff: -BabyBear::ONE,
                col_indices: vec![b],
            },
        ],
        bits,
        alloc,
    )
}

/// `local[a] ≥ min` for a field constant `min` (the `FieldGte{field, min}` shape).
pub fn emit_ge_const(
    a: usize,
    min: BabyBear,
    bits: usize,
    alloc: &mut ColAlloc,
) -> (Vec<ConstraintExpr>, CmpAux) {
    emit_nonneg(
        vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![a],
            },
            PolyTerm {
                coeff: -min,
                col_indices: vec![],
            },
        ],
        bits,
        alloc,
    )
}

/// `local[a] > local[b]`  ==  `local[a] ≥ local[b] + 1`.
pub fn emit_gt(
    a: usize,
    b: usize,
    bits: usize,
    alloc: &mut ColAlloc,
) -> (Vec<ConstraintExpr>, CmpAux) {
    emit_nonneg(
        vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![a],
            },
            PolyTerm {
                coeff: -BabyBear::ONE,
                col_indices: vec![b],
            },
            PolyTerm {
                coeff: -BabyBear::ONE,
                col_indices: vec![],
            }, // − 1
        ],
        bits,
        alloc,
    )
}

/// `local[a] ≤ local[b]`  ==  `local[b] ≥ local[a]`.
pub fn emit_le(
    a: usize,
    b: usize,
    bits: usize,
    alloc: &mut ColAlloc,
) -> (Vec<ConstraintExpr>, CmpAux) {
    emit_ge(b, a, bits, alloc)
}

/// `local[a] < local[b]`  ==  `local[b] > local[a]`.
pub fn emit_lt(
    a: usize,
    b: usize,
    bits: usize,
    alloc: &mut ColAlloc,
) -> (Vec<ConstraintExpr>, CmpAux) {
    emit_gt(b, a, bits, alloc)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bb(x: u32) -> BabyBear {
        BabyBear::new(x)
    }

    /// Every emitted constraint evaluates to 0 (satisfied) against `row`.
    fn accepts(cs: &[ConstraintExpr], row: &[BabyBear]) -> bool {
        cs.iter()
            .all(|c| c.evaluate(row, row, &[]) == BabyBear::ZERO)
    }

    /// A `local` row wide enough for the aux cols, real cols a=0,b=1 preset.
    fn row_for(a: u32, b: u32, aux: &CmpAux) -> Vec<BabyBear> {
        let width = aux.diff.max(*aux.bits.iter().max().unwrap()) + 1;
        let mut row = vec![BabyBear::ZERO; width.max(2)];
        row[0] = bb(a);
        row[1] = bb(b);
        row
    }

    /// Fill diff + bit cols for a claimed non-negative `d` (its honest decomposition).
    fn fill_honest(row: &mut [BabyBear], aux: &CmpAux, d: u32) {
        row[aux.diff] = bb(d);
        for (i, &bc) in aux.bits.iter().enumerate() {
            row[bc] = bb((d >> i) & 1);
        }
    }

    #[test]
    fn ge_honest_accepts() {
        let mut al = ColAlloc::new(2);
        let (cs, aux) = emit_ge(0, 1, 8, &mut al);
        let mut row = row_for(200, 50, &aux);
        fill_honest(&mut row, &aux, 150); // 200 − 50
        assert!(accepts(&cs, &row), "200 ≥ 50 must accept");
    }

    #[test]
    fn ge_boundary_equal_accepts() {
        let mut al = ColAlloc::new(2);
        let (cs, aux) = emit_ge(0, 1, 8, &mut al);
        let mut row = row_for(77, 77, &aux);
        fill_honest(&mut row, &aux, 0);
        assert!(accepts(&cs, &row), "77 ≥ 77 must accept");
    }

    #[test]
    fn ge_cheat_faked_small_diff_rejected() {
        // 50 ≥ 200 is FALSE. Cheat A: pretend diff = 150 with honest-looking bits.
        // Constraint (1) a−b−diff = 50−200−150 ≠ 0 catches it.
        let mut al = ColAlloc::new(2);
        let (cs, aux) = emit_ge(0, 1, 8, &mut al);
        let mut row = row_for(50, 200, &aux);
        fill_honest(&mut row, &aux, 150);
        assert!(
            !accepts(&cs, &row),
            "50 ≥ 200 with a faked diff must reject"
        );
    }

    #[test]
    fn ge_cheat_true_diff_unrepresentable_rejected() {
        // Cheat B: set diff = the TRUE a−b (field-wrapped, ~2^31), bits all zero.
        // Constraint (1) holds, but reconstruction Σbits(0) − diff ≠ 0 catches it.
        let mut al = ColAlloc::new(2);
        let (cs, aux) = emit_ge(0, 1, 8, &mut al);
        let mut row = row_for(50, 200, &aux);
        row[aux.diff] = bb(50) - bb(200); // = p − 150, huge
        for &bc in &aux.bits {
            row[bc] = BabyBear::ZERO;
        }
        assert!(
            !accepts(&cs, &row),
            "unrepresentable true diff must reject at reconstruction"
        );
    }

    #[test]
    fn ge_const_floor() {
        // FieldGte{field, min: 10}: local[a] ≥ 10.
        let mut al = ColAlloc::new(2);
        let (cs, aux) = emit_ge_const(0, bb(10), 8, &mut al);
        // 25 ≥ 10 accepts
        let mut ok = row_for(25, 0, &aux);
        fill_honest(&mut ok, &aux, 15); // 25 − 10
        assert!(accepts(&cs, &ok), "25 ≥ 10 must accept");
        // 3 ≥ 10 rejects (faked diff)
        let mut bad = row_for(3, 0, &aux);
        fill_honest(&mut bad, &aux, 5);
        assert!(!accepts(&cs, &bad), "3 ≥ 10 must reject");
    }

    #[test]
    fn gt_is_strict() {
        // a==b must REJECT for `>` (a−b−1 = −1, no valid witness).
        let mut al = ColAlloc::new(2);
        let (cs, aux) = emit_gt(0, 1, 8, &mut al);
        let mut equal = row_for(77, 77, &aux);
        fill_honest(&mut equal, &aux, 0); // best cheat: diff 0 → (1) gives 77−77−1−0 = −1 ≠ 0
        assert!(!accepts(&cs, &equal), "77 > 77 must reject (strict)");
        // a=78,b=77 accepts: 78−77−1 = 0
        let mut gt = row_for(78, 77, &aux);
        fill_honest(&mut gt, &aux, 0);
        assert!(accepts(&cs, &gt), "78 > 77 must accept");
    }

    #[test]
    fn le_and_lt_derive() {
        // 50 ≤ 200 accepts (b−a = 150).
        let mut al = ColAlloc::new(2);
        let (cs, aux) = emit_le(0, 1, 8, &mut al);
        let mut row = row_for(50, 200, &aux);
        fill_honest(&mut row, &aux, 150);
        assert!(accepts(&cs, &row), "50 ≤ 200 must accept");
        // 200 ≤ 50 rejects.
        let mut al2 = ColAlloc::new(2);
        let (cs2, aux2) = emit_le(0, 1, 8, &mut al2);
        let mut bad = row_for(200, 50, &aux2);
        fill_honest(&mut bad, &aux2, 150);
        assert!(!accepts(&cs2, &bad), "200 ≤ 50 must reject");
    }
}
