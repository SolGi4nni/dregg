//! A co-build harness: it emits the DSL `CircuitDescriptor` constraints AND the
//! single-row witness in lockstep, so columns and witness values cannot drift.
//! `air_accepts` then evaluates the emitted constraints over that row — accept iff every
//! constraint vanishes. Forgery tests `tamper` a named column and re-check.
//!
//! Only constraint kinds the CUSTOM-LEAF lowering carries are used (Polynomial / Binary /
//! ConditionalNonzero / MerkleHash8), so `air_accepts` is a faithful shadow of "the leaf
//! proves" — an AIR built here reaches the door rather than only the DSL evaluator.
//!
//! This is a sibling of `dregg-automatafl`'s builder (same repo, same posture). It is
//! duplicated rather than shared because `dregg-automatafl` is a GAME crate and this one
//! must stay game-free; hoisting one general builder into `circuit/` is the obvious
//! consolidation once a second consumer wants it, and is deliberately not done here (that
//! would edit a read-only foundation crate).

use std::collections::HashMap;

use dregg_circuit::dsl::circuit::{
    CellProgram, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, PolyTerm,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};

pub use crate::field::fb;

/// A polynomial head: `Σ (coeff, cols) + constant`. An empty `cols` is a constant term.
#[derive(Clone, Debug, Default)]
pub struct Head {
    pub terms: Vec<(i128, Vec<usize>)>,
    pub constant: i128,
}

impl Head {
    pub fn zero() -> Self {
        Head {
            terms: vec![],
            constant: 0,
        }
    }
    pub fn c(constant: i128) -> Self {
        Head {
            terms: vec![],
            constant,
        }
    }
    /// `coeff * col`.
    pub fn lin(coeff: i128, col: usize) -> Self {
        Head {
            terms: vec![(coeff, vec![col])],
            constant: 0,
        }
    }
    pub fn add_lin(mut self, coeff: i128, col: usize) -> Self {
        self.terms.push((coeff, vec![col]));
        self
    }
    pub fn add_prod(mut self, coeff: i128, cols: Vec<usize>) -> Self {
        self.terms.push((coeff, cols));
        self
    }
    pub fn add_const(mut self, k: i128) -> Self {
        self.constant += k;
        self
    }
    pub fn scale(mut self, k: i128) -> Self {
        for t in &mut self.terms {
            t.0 *= k;
        }
        self.constant *= k;
        self
    }
    pub fn append(mut self, other: &Head) -> Self {
        self.terms.extend(other.terms.iter().cloned());
        self.constant += other.constant;
        self
    }
}

pub struct Builder {
    pub name: String,
    columns: Vec<ColumnDef>,
    values: Vec<BabyBear>,
    names: Vec<String>,
    constraints: Vec<ConstraintExpr>,
    pub public_input_count: usize,
    pub pis: Vec<BabyBear>,
}

impl Builder {
    pub fn new(name: impl Into<String>) -> Self {
        Builder {
            name: name.into(),
            columns: Vec::new(),
            values: Vec::new(),
            names: Vec::new(),
            constraints: Vec::new(),
            public_input_count: 0,
            pis: Vec::new(),
        }
    }

    pub fn width(&self) -> usize {
        self.columns.len()
    }

    pub fn value(&self, col: usize) -> BabyBear {
        self.values[col]
    }

    pub fn col_by_name(&self, name: &str) -> Option<usize> {
        self.names.iter().position(|n| n == name)
    }

    /// Allocate a fresh column with its honest witness value.
    pub fn alloc(&mut self, name: impl Into<String>, kind: ColumnKind, value: i128) -> usize {
        let idx = self.columns.len();
        let name = name.into();
        self.columns.push(ColumnDef {
            name: name.clone(),
            index: idx,
            kind,
        });
        self.values.push(fb(value));
        self.names.push(name);
        idx
    }

    /// Allocate a column already holding a field element.
    pub fn alloc_f(&mut self, name: impl Into<String>, kind: ColumnKind, value: BabyBear) -> usize {
        let c = self.alloc(name, kind, 0);
        self.values[c] = value;
        c
    }

    /// Append a raw public input (committed, not constraint-bound). Used only for the
    /// door's `[old8 ‖ new8]` state prefix, which the EXECUTOR welds to the cell's roots.
    pub fn add_pi(&mut self, value: BabyBear) {
        self.pis.push(value);
        self.public_input_count = self.pis.len();
    }

    fn push(&mut self, c: ConstraintExpr) {
        self.constraints.push(c);
    }

    /// Assert `head == 0` (a `Polynomial` gate).
    pub fn assert_zero(&mut self, head: &Head) {
        let mut terms: Vec<PolyTerm> = head
            .terms
            .iter()
            .map(|(c, cols)| PolyTerm {
                coeff: fb(*c),
                col_indices: cols.clone(),
            })
            .collect();
        if head.constant % (BABYBEAR_P as i128) != 0 {
            terms.push(PolyTerm {
                coeff: fb(head.constant),
                col_indices: vec![],
            });
        }
        self.push(ConstraintExpr::Polynomial { terms });
    }

    /// Boolean pin (`col*(col-1) == 0`).
    pub fn assert_binary(&mut self, col: usize) {
        self.push(ConstraintExpr::Binary { col });
    }

    /// Pin a column to a constant.
    pub fn assert_const(&mut self, col: usize, value: BabyBear) {
        self.assert_zero(&Head::lin(1, col).add_const(-(value.0 as i128)));
    }

    /// THE RANGE GADGET (bit-decomposition non-negativity). Emits `rbits` boolean columns
    /// and the recomposition `head - Σ 2^k b_k == 0`. A head outside `[0, 2^rbits)` cannot
    /// be recomposed, so the leaf is UNSAT.
    pub fn range_nonneg(&mut self, tag: &str, head: &Head, head_val: i128, rbits: usize) {
        let canon = {
            let p = BABYBEAR_P as i128;
            (((head_val % p) + p) % p) as u128
        };
        let mut recomp = head.clone();
        for k in 0..rbits {
            let bit = ((canon >> k) & 1) as i128;
            let b = self.alloc(format!("{tag}_rb{k}"), ColumnKind::Binary, bit);
            self.assert_binary(b);
            recomp = recomp.add_lin(-(1i128 << k), b);
        }
        self.assert_zero(&recomp);
    }

    /// A boolean column FORCED to `[d >= 0]` for the signed head `d`, via
    /// `range_nonneg(2*ib*d + ib - d - 1)`.
    ///
    /// **Soundness precondition (load-bearing).** `rbits` must be small enough that `d`
    /// and `-d-1` cannot BOTH reduce into `[0, 2^rbits)`. On a full-width ~31-bit value
    /// both always can, and the gadget goes VACUOUS. Callers here keep compared values
    /// under `2^identity_bits` (at most `2^28`) with `rbits = identity_bits + 1`, leaving
    /// `p - d - 1 ≈ 2·10^9` far above `2^29` — see `crate::shape::DEFAULT_IDENTITY_BITS`,
    /// and `ComposeShape::identity_bits_sound`, which refuses a shape that would defeat
    /// this precondition rather than building a circuit whose ordering tooth is decoration.
    pub fn forced_ge0(&mut self, tag: &str, d: &Head, d_val: i128, rbits: usize) -> usize {
        let ib_val = if d_val >= 0 { 1 } else { 0 };
        let ib = self.alloc(format!("{tag}_ib"), ColumnKind::Binary, ib_val);
        self.assert_binary(ib);
        let mut term = Head::zero();
        for (coeff, cols) in &d.terms {
            let mut c2 = vec![ib];
            c2.extend(cols.iter().copied());
            term = term.add_prod(2 * coeff, c2);
        }
        term = term.add_prod(2 * d.constant, vec![ib]);
        term = term.add_lin(1, ib);
        term = term.append(&d.clone().scale(-1));
        term = term.add_const(-1);
        let term_val = if d_val >= 0 { d_val } else { -d_val - 1 };
        self.range_nonneg(&format!("{tag}_t"), &term, term_val, rbits);
        ib
    }

    /// `ConditionalNonzero`: when `selector != 0`, require `value != 0` (witnessed inverse).
    pub fn cond_nonzero(&mut self, tag: &str, selector_col: usize, value_col: usize) {
        let inv_val = if self.values[selector_col] != BabyBear::ZERO {
            self.values[value_col].inverse().unwrap_or(BabyBear::ZERO)
        } else {
            BabyBear::ZERO
        };
        let inv = self.alloc_f(format!("{tag}_inv"), ColumnKind::Value, inv_val);
        self.push(ConstraintExpr::ConditionalNonzero {
            selector_col,
            value_col,
            inverse_col: inv,
        });
    }

    /// A fresh column pinned to `a*b`.
    pub fn alloc_prod(&mut self, name: &str, a: usize, b: usize) -> usize {
        let v = self.values[a] * self.values[b];
        let out = self.alloc_f(name, ColumnKind::Value, v);
        self.assert_zero(&Head::lin(-1, out).add_prod(1, vec![a, b]));
        out
    }

    /// A fresh column pinned to a head's value.
    pub fn alloc_head(&mut self, name: &str, head: &Head, value: BabyBear) -> usize {
        let out = self.alloc_f(name, ColumnKind::Value, value);
        self.assert_zero(&head.clone().add_lin(-1, out));
        out
    }

    /// A Poseidon2 `MerkleHash8` site: `output_cols[0..8] == cap_node8(left_cols[0..8],
    /// right_cols[0..8])` — the native arity-16 `node8` compression, all 8 output lanes
    /// bound. Lowers to ONE `TID_P2` chip lookup whose 8 outputs are program-owned
    /// (`ChipOut::Lanes8`), so it costs ZERO lane columns while binding the full 8-felt
    /// (~124-bit) digest — the single-output `Hash4to1` form squeezed lane 0 alone and paid
    /// 7 witness columns per site to do it.
    pub fn push_merkle_hash8(
        &mut self,
        output_cols: [usize; 8],
        left_cols: [usize; 8],
        right_cols: [usize; 8],
    ) {
        self.push(ConstraintExpr::MerkleHash8 {
            output_cols,
            left_cols,
            right_cols,
        });
    }

    /// The honest `cap_node8` of two 8-felt column groups' current witness values.
    pub fn cap_node8_value(&self, left: [usize; 8], right: [usize; 8]) -> [BabyBear; 8] {
        dregg_circuit::cap_root::cap_node8(
            core::array::from_fn(|i| self.values[left[i]]),
            core::array::from_fn(|i| self.values[right[i]]),
        )
    }

    /// Bind an existing column to a FRESH public input, pinning `col == pi[index]`.
    /// Returns the PI index. PIs are appended in call order, so the caller controls the
    /// layout.
    pub fn bind_pi(&mut self, col: usize) -> usize {
        let pi_index = self.pis.len();
        self.pis.push(self.values[col]);
        self.public_input_count = self.pis.len();
        self.push(ConstraintExpr::PiBinding { col, pi_index });
        pi_index
    }

    // -------- witness self-evaluation (the `air_accepts` shadow) --------

    /// `(constraint_index, residual)` for every constraint that does NOT vanish.
    pub fn failing(&self) -> Vec<(usize, BabyBear)> {
        let row = &self.values;
        let mut out = Vec::new();
        for (i, c) in self.constraints.iter().enumerate() {
            let r = c.evaluate(row, row, &self.pis);
            if r != BabyBear::ZERO {
                out.push((i, r));
            }
        }
        out
    }

    /// The AIR accepts the current witness iff no constraint has a nonzero residual.
    pub fn air_accepts(&self) -> bool {
        self.failing().is_empty()
    }

    /// Overwrite a column's witness value (a forgery), returning the previous value.
    pub fn tamper(&mut self, col: usize, value: i128) -> BabyBear {
        let prev = self.values[col];
        self.values[col] = fb(value);
        prev
    }

    pub fn set_value(&mut self, col: usize, value: BabyBear) {
        self.values[col] = value;
    }

    // -------- lowering to the prove path --------

    pub fn max_degree(&self) -> usize {
        self.constraints
            .iter()
            .map(|c| c.degree())
            .max()
            .unwrap_or(1)
    }

    pub fn descriptor(&self) -> CircuitDescriptor {
        CircuitDescriptor {
            name: self.name.clone(),
            trace_width: self.columns.len(),
            max_degree: self.max_degree().max(1),
            columns: self.columns.clone(),
            constraints: self.constraints.clone(),
            boundaries: vec![],
            public_input_count: self.public_input_count,
            lookup_tables: vec![],
        }
    }

    pub fn cellprogram(&self) -> CellProgram {
        CellProgram::new(self.descriptor(), 1)
    }

    /// The trace witness (`col name -> per-row values`, constant across `num_rows`).
    pub fn trace_witness(&self, num_rows: usize) -> HashMap<String, Vec<BabyBear>> {
        let mut w = HashMap::new();
        for (i, col) in self.columns.iter().enumerate() {
            w.insert(col.name.clone(), vec![self.values[i]; num_rows]);
        }
        w
    }

    pub fn constraint_count(&self) -> usize {
        self.constraints.len()
    }

    /// Poseidon2 chip sites emitted — the fuel meter (`ComposeShape::hash_sites` is its
    /// shape-only twin, and `tests/size.rs` pins the two together). Each `MerkleHash8` is
    /// ONE arity-16 `node8` permutation.
    pub fn hash_site_count(&self) -> usize {
        self.constraints
            .iter()
            .filter(|c| matches!(c, ConstraintExpr::MerkleHash8 { .. }))
            .count()
    }
}
