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
//! ## Honest scope — what this covers, precisely
//! The `dregg-cell` ordering teeth are all **same-post-state** comparisons —
//! `FieldGte{index,value}`, `FieldLte{index,value}`, `FieldLteField{left,right}`,
//! `FieldLteOther{index,other,delta}` (the capacity / no-underflow cross-slot bounds)
//! — so this crate's same-row gadget is the right shape for every one of them (a
//! `FieldLteOther` capacity bound `head − tail ≤ cap` is `emit_nonneg([cap] + [tail] −
//! [head] ≥ 0)`, `FieldLteField` is [`emit_le`], `FieldGte`-const is [`emit_ge_const`]).
//!
//! **One caveat the wire-in must honor (not laundered):** those slots are `u64`
//! (big-endian, lifted to `i128`), while a comparison here is over values
//! `< 2^bits < 2^31` — a **single BabyBear limb**. Small domains (HP, scene index,
//! budget, queue depth) fit one limb and lower directly via [`emit_ge`] & friends.
//! A **full-`u64` slot spans multiple limbs**: [`emit_ge_multilimb`] /
//! [`emit_ge_const_multilimb`] handle it via per-limb comparison + a borrow chain
//! (`A ≥ C` iff the final borrow is 0). The compiler supplies the trace's slot→limb
//! layout; this crate supplies both the per-limb primitive and the multi-limb chain.
//! If a native `RangeLookup`/`Lte` `ConstraintExpr` variant is later added, this API is
//! unchanged — only the internal lowering swaps.

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

/// Range-check `local[col] ∈ [0, 2^bits)` by bit-decomposition — the shared kernel of
/// every comparison. Returns the constraints + the allocated bit columns; the caller
/// sets `local[bits[i]] = i-th bit of local[col]`.
pub fn emit_range(
    col: usize,
    bits: usize,
    alloc: &mut ColAlloc,
) -> (Vec<ConstraintExpr>, Vec<usize>) {
    assert!(
        (1..31).contains(&bits),
        "range `bits` must be in 1..31 for BabyBear; got {bits}"
    );
    let bit_cols = alloc.alloc_n(bits);
    let mut cs = Vec::with_capacity(bits + 1);
    for &bc in &bit_cols {
        cs.push(ConstraintExpr::Binary { col: bc });
    }
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
        col_indices: vec![col],
    });
    cs.push(ConstraintExpr::Polynomial { terms: recon });
    (cs, bit_cols)
}

/// A right-hand operand limb for a multi-limb comparison: a witness column, or a
/// compile-time constant (for `FieldGte`/`FieldLte` against a fixed bound).
#[derive(Clone, Copy)]
pub enum Operand {
    Col(usize),
    Const(u32),
}

/// The witness columns a multi-limb comparison introduces, per limb: the result limb,
/// its range bits, and the outgoing borrow. `A ≥ C` iff `borrows.last()` is 0.
pub struct MultiLimbAux {
    pub results: Vec<usize>,
    pub result_bits: Vec<Vec<usize>>,
    pub borrows: Vec<usize>,
}

/// `A ≥ C` for `u64`-scale values held as **little-endian `limb_bits`-bit limbs**
/// (`A = Σ a_limbs[i]·2^{i·limb_bits}`), with `C` per-limb as columns or constants.
/// Borrow-chain subtraction: each limb `i` yields a range-checked result limb
/// `r_i ∈ [0, 2^limb_bits)` and a boolean borrow, enforcing
/// `a_i − c_i − borrow_in + 2^limb_bits·borrow_out − r_i = 0`; then **`A ≥ C` iff the
/// final borrow is 0** (enforced by a `== 0` constraint on the MSB borrow). This is the
/// full-`u64` completion of [`emit_ge`]: a `< 2^31` domain is just the one-limb case.
///
/// ## Soundness (against a malicious prover, not just honest-fill)
/// The borrow chain is FORCED, not chosen. At each limb, constraint (1)
/// `a_i − c_i − b_in + base·b_out − r_i = 0`, plus `r_i ∈ [0, base)` (the range-check)
/// and `b_out ∈ {0,1}` (Binary), admit EXACTLY ONE `b_out`: writing the integer
/// `t = a_i − c_i − b_in ∈ [−base, base)`, `b_out = 0` needs `r_i = t` (in range only if
/// `t ≥ 0`) and `b_out = 1` needs `r_i = t + base` (in range only if `t < 0`). A
/// field-wrapped `r_i` (e.g. `t < 0` taken with `b_out = 0`, giving `r_i ≡ t + p ≈ p`)
/// is far outside `[0, base)`, so the range-check rejects it. Hence every `(r_i, b_out)`
/// is the honest borrow, the final borrow is 1 **iff** `A < C`, and the `== 0`
/// constraint on it rejects `A < C` — a prover cannot fake it (exercised by
/// `multilimb_cheat_fake_final_borrow_rejected`).
pub fn emit_ge_multilimb_ops(
    a_limbs: &[usize],
    c: &[Operand],
    limb_bits: usize,
    alloc: &mut ColAlloc,
) -> (Vec<ConstraintExpr>, MultiLimbAux) {
    assert_eq!(a_limbs.len(), c.len(), "operand limb counts must match");
    assert!(!a_limbs.is_empty(), "need at least one limb");
    assert!((1..31).contains(&limb_bits), "limb_bits must be in 1..31");
    let base = BabyBear::new(1u32 << limb_bits);
    let mut cs = Vec::new();
    let mut results = Vec::new();
    let mut result_bits = Vec::new();
    let mut borrows = Vec::new();
    let mut prev_borrow: Option<usize> = None;
    for (i, &a_i) in a_limbs.iter().enumerate() {
        let r_i = alloc.alloc();
        let b_out = alloc.alloc();
        // a_i − c_i − borrow_in + base·b_out − r_i = 0
        let mut terms = vec![PolyTerm {
            coeff: BabyBear::ONE,
            col_indices: vec![a_i],
        }];
        match c[i] {
            Operand::Col(cc) => terms.push(PolyTerm {
                coeff: -BabyBear::ONE,
                col_indices: vec![cc],
            }),
            Operand::Const(k) => terms.push(PolyTerm {
                coeff: -BabyBear::new(k),
                col_indices: vec![],
            }),
        }
        if let Some(pb) = prev_borrow {
            terms.push(PolyTerm {
                coeff: -BabyBear::ONE,
                col_indices: vec![pb],
            });
        }
        terms.push(PolyTerm {
            coeff: base,
            col_indices: vec![b_out],
        });
        terms.push(PolyTerm {
            coeff: -BabyBear::ONE,
            col_indices: vec![r_i],
        });
        cs.push(ConstraintExpr::Polynomial { terms });
        // r_i ∈ [0, 2^limb_bits)
        let (rcs, rbits) = emit_range(r_i, limb_bits, alloc);
        cs.extend(rcs);
        // b_out is a bit
        cs.push(ConstraintExpr::Binary { col: b_out });
        results.push(r_i);
        result_bits.push(rbits);
        borrows.push(b_out);
        prev_borrow = Some(b_out);
    }
    // A ≥ C  ⟺  final borrow == 0
    let last = *borrows.last().unwrap();
    cs.push(ConstraintExpr::Polynomial {
        terms: vec![PolyTerm {
            coeff: BabyBear::ONE,
            col_indices: vec![last],
        }],
    });
    (
        cs,
        MultiLimbAux {
            results,
            result_bits,
            borrows,
        },
    )
}

/// `A ≥ C` where both are column-limb values.
pub fn emit_ge_multilimb(
    a_limbs: &[usize],
    c_limbs: &[usize],
    limb_bits: usize,
    alloc: &mut ColAlloc,
) -> (Vec<ConstraintExpr>, MultiLimbAux) {
    let c: Vec<Operand> = c_limbs.iter().map(|&c| Operand::Col(c)).collect();
    emit_ge_multilimb_ops(a_limbs, &c, limb_bits, alloc)
}

/// `A ≥ const`, `const` given as little-endian `limb_bits`-bit limbs (`FieldGte`).
pub fn emit_ge_const_multilimb(
    a_limbs: &[usize],
    c_const_limbs: &[u32],
    limb_bits: usize,
    alloc: &mut ColAlloc,
) -> (Vec<ConstraintExpr>, MultiLimbAux) {
    let c: Vec<Operand> = c_const_limbs.iter().map(|&k| Operand::Const(k)).collect();
    emit_ge_multilimb_ops(a_limbs, &c, limb_bits, alloc)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bb(x: u32) -> BabyBear {
        BabyBear::new(x)
    }

    /// Build + fill a witness row for a multi-limb `A ≥ C` over column limbs
    /// (a at 0..n, c at n..2n), computing the honest borrow-chain subtraction.
    fn build_ml_row(a: &[u32], c: &[u32], aux: &MultiLimbAux, limb_bits: usize) -> Vec<BabyBear> {
        let n = a.len();
        let base = 1i64 << limb_bits;
        let maxcol = aux
            .results
            .iter()
            .chain(aux.borrows.iter())
            .chain(aux.result_bits.iter().flatten())
            .copied()
            .max()
            .unwrap()
            .max(2 * n - 1)
            + 1;
        let mut row = vec![BabyBear::ZERO; maxcol];
        for i in 0..n {
            row[i] = bb(a[i]);
            row[n + i] = bb(c[i]);
        }
        let mut borrow = 0i64;
        for i in 0..n {
            let diff = a[i] as i64 - c[i] as i64 - borrow;
            let (r, bo) = if diff < 0 {
                (diff + base, 1i64)
            } else {
                (diff, 0)
            };
            row[aux.results[i]] = bb(r as u32);
            for (j, &bc) in aux.result_bits[i].iter().enumerate() {
                row[bc] = bb(((r as u32) >> j) & 1);
            }
            row[aux.borrows[i]] = bb(bo as u32);
            borrow = bo;
        }
        row
    }

    #[test]
    fn multilimb_ge_honest_accepts() {
        // 2 limbs of 8 bits, little-endian. A = 300 (44,1), C = 100 (100,0).
        let mut al = ColAlloc::new(4);
        let (cs, aux) = emit_ge_multilimb(&[0, 1], &[2, 3], 8, &mut al);
        let row = build_ml_row(&[44, 1], &[100, 0], &aux, 8);
        assert!(accepts(&cs, &row), "300 ≥ 100 must accept");
    }

    #[test]
    fn multilimb_ge_less_rejects_via_final_borrow() {
        // A = 100 (100,0), C = 300 (44,1) — A < C, so the MSB borrow is 1 and the
        // final `borrow == 0` constraint fails. No witness can avoid it.
        let mut al = ColAlloc::new(4);
        let (cs, aux) = emit_ge_multilimb(&[0, 1], &[2, 3], 8, &mut al);
        let row = build_ml_row(&[100, 0], &[44, 1], &aux, 8);
        assert!(
            !accepts(&cs, &row),
            "100 ≥ 300 must reject (final borrow = 1)"
        );
    }

    #[test]
    fn multilimb_ge_boundary_equal_accepts() {
        let mut al = ColAlloc::new(4);
        let (cs, aux) = emit_ge_multilimb(&[0, 1], &[2, 3], 8, &mut al);
        let row = build_ml_row(&[44, 1], &[44, 1], &aux, 8);
        assert!(accepts(&cs, &row), "300 ≥ 300 must accept");
    }

    #[test]
    fn multilimb_ge_const_floor() {
        // A = 500 (244,1) ≥ const 256 (0,1): the FieldGte{index, value} shape on a u64.
        let mut al = ColAlloc::new(2); // only a limbs are columns (0,1); c is constant
        let (cs, aux) = emit_ge_const_multilimb(&[0, 1], &[0, 1], 8, &mut al);
        // build row: a at 0,1; fill aux from the honest chain vs the const.
        let a = [244u32, 1];
        let c = [0u32, 1];
        let maxcol = aux
            .results
            .iter()
            .chain(aux.borrows.iter())
            .chain(aux.result_bits.iter().flatten())
            .copied()
            .max()
            .unwrap()
            .max(1)
            + 1;
        let mut row = vec![BabyBear::ZERO; maxcol];
        row[0] = bb(a[0]);
        row[1] = bb(a[1]);
        let base = 1i64 << 8;
        let mut borrow = 0i64;
        for i in 0..2 {
            let diff = a[i] as i64 - c[i] as i64 - borrow;
            let (r, bo) = if diff < 0 {
                (diff + base, 1i64)
            } else {
                (diff, 0)
            };
            row[aux.results[i]] = bb(r as u32);
            for (j, &bc) in aux.result_bits[i].iter().enumerate() {
                row[bc] = bb(((r as u32) >> j) & 1);
            }
            row[aux.borrows[i]] = bb(bo as u32);
            borrow = bo;
        }
        assert!(accepts(&cs, &row), "500 ≥ 256 must accept");
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

    // ── adversarial soundness: a MALICIOUS prover, not just honest-fill ──────────

    #[test]
    fn ge_cheat_tampered_bit_rejected() {
        // Honest diff (200−50 = 150) but ONE decomposition bit flipped. The flipped bit is still a
        // valid bit (Binary passes), but Σ2^i·bit now ≠ diff, so the reconstruction rejects.
        let mut al = ColAlloc::new(2);
        let (cs, aux) = emit_ge(0, 1, 8, &mut al);
        let mut row = row_for(200, 50, &aux);
        fill_honest(&mut row, &aux, 150);
        row[aux.bits[0]] = bb(1); // 150 is even → bit0 was 0; flipping it makes Σbits = 151 ≠ 150
        assert!(
            !accepts(&cs, &row),
            "a flipped decomposition bit must reject at reconstruction"
        );
    }

    #[test]
    fn multilimb_cheat_fake_final_borrow_rejected() {
        // THE adversarial soundness case. A = 100 (limbs 100,0) < C = 300 (limbs 44,1). A malicious
        // prover fakes the FINAL borrow = 0 (claiming A ≥ C). Constraint (1) on the top limb then
        // FORCES r1 = a1 − c1 − b_in = 0 − 1 − 0 = −1 ≡ p−1, which is NOT in [0, 2^8) — so the
        // range-check on r1 rejects. A faked borrow cannot survive: exactly one b_out keeps r in
        // range, so the borrow chain is forced, not the prover's to choose.
        let mut al = ColAlloc::new(4);
        let (cs, aux) = emit_ge_multilimb(&[0, 1], &[2, 3], 8, &mut al);
        let maxcol = aux
            .results
            .iter()
            .chain(aux.borrows.iter())
            .chain(aux.result_bits.iter().flatten())
            .copied()
            .max()
            .unwrap()
            .max(3)
            + 1;
        let mut row = vec![BabyBear::ZERO; maxcol];
        row[0] = bb(100);
        row[1] = bb(0);
        row[2] = bb(44);
        row[3] = bb(1);
        // limb 0 honest: r0 = 100 − 44 − 0 = 56, b_out0 = 0.
        row[aux.results[0]] = bb(56);
        for (j, &bc) in aux.result_bits[0].iter().enumerate() {
            row[bc] = bb((56u32 >> j) & 1);
        }
        row[aux.borrows[0]] = bb(0);
        // limb 1 CHEAT: fake b_out1 = 0 → constraint (1) forces r1 = 0 − 1 − 0 = p−1 (out of range).
        row[aux.borrows[1]] = bb(0);
        row[aux.results[1]] = bb(0) - bb(1); // p−1
        for &bc in &aux.result_bits[1] {
            row[bc] = BabyBear::ZERO;
        }
        assert!(
            !accepts(&cs, &row),
            "faked final borrow (A<C claimed A≥C) must reject via the r1 range-check"
        );
    }

    // ── real-u64-scale + edge coverage ──────────────────────────────────────────

    #[test]
    fn multilimb_u64_full_borrow_propagation() {
        // 2^48 (limbs [0,0,0,1]) ≥ 1 (limbs [1,0,0,0]) at 4×16-bit — a borrow propagates through
        // ALL four limbs, exercising the full-u64 chain.
        let mut al = ColAlloc::new(8);
        let (cs, aux) = emit_ge_multilimb(&[0, 1, 2, 3], &[4, 5, 6, 7], 16, &mut al);
        let row = build_ml_row(&[0, 0, 0, 1], &[1, 0, 0, 0], &aux, 16);
        assert!(
            accepts(&cs, &row),
            "2^48 ≥ 1 (borrow through 4 limbs) must accept"
        );
        let mut al2 = ColAlloc::new(8);
        let (cs2, aux2) = emit_ge_multilimb(&[0, 1, 2, 3], &[4, 5, 6, 7], 16, &mut al2);
        let row2 = build_ml_row(&[1, 0, 0, 0], &[0, 0, 0, 1], &aux2, 16);
        assert!(!accepts(&cs2, &row2), "1 ≥ 2^48 must reject");
    }

    #[test]
    fn multilimb_n1_agrees_with_single() {
        // A one-limb multi-limb comparison must agree with the single-limb gadget.
        let mut al = ColAlloc::new(2);
        let (cs, aux) = emit_ge_multilimb(&[0], &[1], 8, &mut al);
        assert!(
            accepts(&cs, &build_ml_row(&[200], &[50], &aux, 8)),
            "1-limb 200 ≥ 50 accepts"
        );
        let mut al2 = ColAlloc::new(2);
        let (cs2, aux2) = emit_ge_multilimb(&[0], &[1], 8, &mut al2);
        assert!(
            !accepts(&cs2, &build_ml_row(&[50], &[200], &aux2, 8)),
            "1-limb 50 ≥ 200 rejects"
        );
    }

    #[test]
    fn bits_one_minimal_domain() {
        // The minimal domain: single-bit (0/1) values.
        let mut al = ColAlloc::new(2);
        let (cs, aux) = emit_ge(0, 1, 1, &mut al);
        let mut ok = row_for(1, 0, &aux);
        fill_honest(&mut ok, &aux, 1);
        assert!(accepts(&cs, &ok), "1 ≥ 0 (bits=1) accepts");
        let mut al2 = ColAlloc::new(2);
        let (cs2, aux2) = emit_ge(0, 1, 1, &mut al2);
        let mut bad = row_for(0, 1, &aux2);
        fill_honest(&mut bad, &aux2, 1); // best cheat: claim diff = 1
        assert!(!accepts(&cs2, &bad), "0 ≥ 1 (bits=1) rejects");
    }
}
