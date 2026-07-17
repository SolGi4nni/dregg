//! A co-build harness: it emits the DSL `CircuitDescriptor` constraints AND the
//! single-row witness in lockstep, so columns and witness values can never drift.
//! Every gadget records the honest witness value it computed from the reference,
//! then `air_accepts` evaluates the emitted constraints over that row — accept iff
//! every constraint vanishes. Forgery tests `tamper` a named column and re-check.
//!
//! Only PURE-LOCAL algebraic `ConstraintExpr` kinds are used (Polynomial / Binary),
//! which lower one-to-one to IR-v2 `Base(Gate(..))` bodies in
//! `cellprogram_to_descriptor2` and are checked identically by the DSL evaluator
//! here and by the real STARK quotient/FRI on the prove path — so `air_accepts`
//! is a faithful shadow of "the leaf proves".

use std::collections::HashMap;

use dregg_circuit::dsl::circuit::{
    CellProgram, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, PolyTerm,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};

/// Canonical `BabyBear` of a signed integer (handles negatives, e.g. `-1 -> p-1`).
pub fn fb(x: i128) -> BabyBear {
    let p = BABYBEAR_P as i128;
    BabyBear::new((((x % p) + p) % p) as u32)
}

/// A linear (or product) head: `Σ (coeff, cols) + constant`. `cols` empty = constant term.
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
    values: Vec<BabyBear>, // parallel to columns; the single-row witness
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

    /// Allocate a fresh column with a witness value (signed integer, reduced mod p).
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

    pub fn add_pi(&mut self, value: i128) {
        self.pis.push(fb(value));
        self.public_input_count = self.pis.len();
    }

    fn push(&mut self, c: ConstraintExpr) {
        self.constraints.push(c);
    }

    /// Assert `Σ head == 0` (a `Polynomial` gate).
    pub fn assert_zero(&mut self, head: &Head) {
        let mut terms: Vec<PolyTerm> = head
            .terms
            .iter()
            .filter(|(c, _)| *c % (BABYBEAR_P as i128) != 0 || true) // keep all; coeff may be 0 only if intended
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

    /// `∏_{s in set} (col - s) == 0` (membership; degree |set|).
    pub fn assert_member(&mut self, col: usize, set: &[i128]) {
        // Expand the product into a Polynomial.
        let mut poly: Vec<PolyTerm> = vec![PolyTerm {
            coeff: BabyBear::ONE,
            col_indices: vec![],
        }];
        for &s in set {
            let mut next: Vec<PolyTerm> = Vec::new();
            for t in &poly {
                let mut with_col = t.col_indices.clone();
                with_col.push(col);
                next.push(PolyTerm {
                    coeff: t.coeff,
                    col_indices: with_col,
                });
                next.push(PolyTerm {
                    coeff: t.coeff * fb(-s),
                    col_indices: t.col_indices.clone(),
                });
            }
            poly = next;
        }
        self.push(ConstraintExpr::Polynomial { terms: poly });
    }

    /// A one-hot selector vector of `k` bits, witnessed one at `hot`, pinned so that
    /// `Σ j*sel_j == index_head`. Returns the selector column indices. (Does NOT bind
    /// a read value; use [`Self::one_hot_read`] for the full read.)
    pub fn one_hot(&mut self, tag: &str, k: usize, hot: usize, index_head: &Head) -> Vec<usize> {
        let mut sel = Vec::with_capacity(k);
        for j in 0..k {
            let v = if j == hot { 1 } else { 0 };
            let c = self.alloc(format!("{tag}_sel{j}"), ColumnKind::Binary, v);
            self.assert_binary(c);
            sel.push(c);
        }
        // Σ sel == 1.
        let mut sum = Head::c(-1);
        for &c in &sel {
            sum = sum.add_lin(1, c);
        }
        self.assert_zero(&sum);
        // Σ j*sel_j - index_head == 0.
        let mut idx = Head::zero();
        for (j, &c) in sel.iter().enumerate() {
            idx = idx.add_lin(j as i128, c);
        }
        idx = idx.append(&index_head.clone().scale(-1));
        self.assert_zero(&idx);
        sel
    }

    /// Random-access board read: `value_col == board[index]`, where `index` is pinned
    /// to `index_head` by a one-hot selector. `board_cols[index_val]` must equal the
    /// witnessed value of `value_col` (the caller computed both from the reference).
    /// Degree 2 (the `Σ sel_j*board_j` product).
    pub fn one_hot_read(
        &mut self,
        tag: &str,
        board_cols: &[usize],
        index_val: usize,
        index_head: &Head,
        value_col: usize,
    ) {
        let sel = self.one_hot(tag, board_cols.len(), index_val, index_head);
        // Σ sel_j * board_j - value_col == 0.
        let mut rd = Head::zero();
        for (j, &s) in sel.iter().enumerate() {
            rd = rd.add_prod(1, vec![s, board_cols[j]]);
        }
        rd = rd.add_lin(-1, value_col);
        self.assert_zero(&rd);
    }

    /// THE RANGE GADGET (bit-decomposition non-negativity, per `compiler.rs`).
    /// Emit `rbits` boolean columns and the recomposition `head - Σ 2^k b_k == 0`.
    /// The honest `head_val` (which must be `0 <= head_val < 2^rbits`) fills the bits;
    /// a negative/over-range head cannot be recomposed by any bits, so the leaf is
    /// UNSAT — a genuine non-negativity proof sound through the STARK/FRI quotient.
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

    /// A boolean column FORCED to equal `[d >= 0]` for the signed head `d`. Enforced
    /// by `range_nonneg(2*ib*d + ib - d - 1)`: when `d >= 0` only `ib = 1` keeps the
    /// term `>= 0` (`= d`); when `d < 0` only `ib = 0` does (`= -d-1`). So the bit is
    /// pinned to the true comparison — a forged bit makes the range gadget UNSAT.
    pub fn forced_ge0(&mut self, tag: &str, d: &Head, d_val: i128, rbits: usize) -> usize {
        let ib_val = if d_val >= 0 { 1 } else { 0 };
        let ib = self.alloc(format!("{tag}_ib"), ColumnKind::Binary, ib_val);
        self.assert_binary(ib);
        // term = 2*ib*d + ib - d - 1
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

    /// Range-pin a board coordinate to `0 ..= max` by BIT-DECOMPOSITION instead of the
    /// degree-`(max+1)` vanishing product [`Self::assert_member`] would emit for the set
    /// `0..=max`. Two [`Self::range_nonneg`] gadgets do it in degree ≤ 2:
    ///   * `col = Σ 2^k·b_k` over `rbits` boolean bits ⇒ `0 ≤ col < 2^rbits` (the lower edge);
    ///   * `max − col = Σ 2^k·b'_k` ⇒ `col ≤ max` (the upper edge — a HARD non-negativity
    ///     assertion, so a coordinate past `max` has no satisfying bits, exactly as the
    ///     membership product rejected it).
    /// `rbits` is the minimal width covering `0..=max`. Same range as `assert_member(0..=max)`,
    /// but NO emitted constraint grows with the board: an 11×11 board's `0..=10` coordinate pin
    /// is degree ≤ 2 rather than degree 11 (over `MAX_CONSTRAINT_DEGREE = 8`). This is what makes
    /// a larger board legal on the degree axis; the receipt is unchanged (same coordinate columns,
    /// same range). Lighter than a `forced_ge0` upper bound (which also witnesses a comparison bit
    /// this hard pin does not need) — the column budget the deployed n=5 leaves prove under.
    pub fn decompose_coord_le(&mut self, tag: &str, col: usize, max: i128) {
        debug_assert!(max >= 0, "coordinate upper bound must be non-negative");
        // Minimal bit width covering 0..=max (2^rbits > max).
        let mut rbits = 1usize;
        while (1i128 << rbits) <= max {
            rbits += 1;
        }
        let val = self.value(col).0 as i128;
        // Lower edge: col = Σ 2^k·b_k  ⇒  0 ≤ col < 2^rbits.
        self.range_nonneg(&format!("{tag}_lo"), &Head::lin(1, col), val, rbits);
        // Upper edge: max − col ≥ 0  ⇒  col ≤ max.
        self.range_nonneg(
            &format!("{tag}_hi"),
            &Head::c(max).add_lin(-1, col),
            max - val,
            rbits,
        );
    }

    /// `ConditionalNonzero`: when `selector != 0`, require `value != 0` (via a witnessed
    /// inverse). `value_val` is the honest value (used to fill the inverse; `0` if the
    /// selector is off so `value` may legitimately be zero).
    pub fn cond_nonzero(
        &mut self,
        tag: &str,
        selector_col: usize,
        value_col: usize,
        value_val: i128,
    ) {
        let inv_val: i128 = if self.values[selector_col] != BabyBear::ZERO {
            // value must be nonzero; witness its inverse.
            fb(value_val).inverse().map(|x| x.0 as i128).unwrap_or(0)
        } else {
            0
        };
        let inv = self.alloc(format!("{tag}_inv"), ColumnKind::Value, inv_val);
        self.push(ConstraintExpr::ConditionalNonzero {
            selector_col,
            value_col,
            inverse_col: inv,
        });
    }

    /// A one-hot selector gated by `gate_col` (a bit): the selectors sum to `gate`
    /// (all zero when the gate is off), and when on they one-hot at `index_head`.
    /// Returns the selector columns. `hot` is the honest hot index (ignored if the
    /// gate is off in the witness).
    pub fn one_hot_gated(
        &mut self,
        tag: &str,
        k: usize,
        gate_col: usize,
        hot: usize,
        index_head: &Head,
    ) -> Vec<usize> {
        let on = self.values[gate_col] != BabyBear::ZERO;
        let mut sel = Vec::with_capacity(k);
        for j in 0..k {
            let v = if on && j == hot { 1 } else { 0 };
            let c = self.alloc(format!("{tag}_sel{j}"), ColumnKind::Binary, v);
            self.assert_binary(c);
            sel.push(c);
        }
        // Σ sel - gate == 0.
        let mut s = Head::lin(-1, gate_col);
        for &c in &sel {
            s = s.add_lin(1, c);
        }
        self.assert_zero(&s);
        // Σ j*sel_j - gate*index_head == 0.
        let mut idx = Head::zero();
        for (j, &c) in sel.iter().enumerate() {
            idx = idx.add_lin(j as i128, c);
        }
        for (coeff, cols) in &index_head.terms {
            let mut cc = vec![gate_col];
            cc.extend(cols.iter().copied());
            idx = idx.add_prod(-coeff, cc);
        }
        idx = idx.add_prod(-index_head.constant, vec![gate_col]);
        self.assert_zero(&idx);
        sel
    }

    /// Gated random-access read: `value_col == board[index]` when `gate` is on, else
    /// `value_col == 0` (the OOB/wall convention). Selectors sum to `gate`.
    pub fn one_hot_read_gated(
        &mut self,
        tag: &str,
        board_cols: &[usize],
        gate_col: usize,
        index_val: usize,
        index_head: &Head,
        value_col: usize,
    ) {
        let sel = self.one_hot_gated(tag, board_cols.len(), gate_col, index_val, index_head);
        // Σ sel_j*board_j - value_col == 0.
        let mut rd = Head::zero();
        for (j, &s) in sel.iter().enumerate() {
            rd = rd.add_prod(1, vec![s, board_cols[j]]);
        }
        rd = rd.add_lin(-1, value_col);
        self.assert_zero(&rd);
    }

    /// Gated read that REUSES an already-proven one-hot `sel` (over the same board),
    /// shifted by a COMPILE-TIME flat offset `off`: `value_col == board[hot + off]` when
    /// `gate` is on (and `hot + off` is in range), else `value_col == 0`. Allocates NO new
    /// selector columns — the constraint is `value - Σ_{j: 0 ≤ j+off < k} gate·sel[j]·board[j+off]`.
    ///
    /// This is THE RAY-SCAN reduction: the four rays read cells at COMPILE-TIME offsets from
    /// the auto pin, so they reuse the single `sel_auto` one-hot instead of allocating a fresh
    /// n² one-hot per step — collapsing the 4n³ selector blowup to n². Soundness is UNCHANGED:
    /// `sel` is the same one-hot pinned to the auto position, so the read is the genuine board
    /// cell `auto + off`; the `gate` (the in-bounds bit, itself range-gadget-forced) zeroes an
    /// out-of-bounds step exactly as the fresh-one-hot read did. Degree 3 (`gate·sel·board`).
    pub fn shifted_read_gated(
        &mut self,
        sel: &[usize],
        board_cols: &[usize],
        gate_col: usize,
        off: i128,
        value_col: usize,
    ) {
        let k = board_cols.len();
        let mut rd = Head::lin(1, value_col);
        for (j, &s) in sel.iter().enumerate() {
            let t = j as i128 + off;
            if t >= 0 && (t as usize) < k {
                rd = rd.add_prod(-1, vec![gate_col, s, board_cols[t as usize]]);
            }
        }
        self.assert_zero(&rd);
    }

    // -------- row×column √n reads/writes (C.2) --------
    //
    // A board read `board[y·n+x]` addressed by ONE n²-wide one-hot costs n² selector
    // columns. The row×column form pins the row and column INDEPENDENTLY with two n-wide
    // one-hots `sel_row[y]` (pinned to `y_head`) and `sel_col[x]` (pinned to `x_head`) —
    // 2n selectors, not n² — and addresses cell `(x,y)` by the PRODUCT `sel_row[y]·sel_col[x]`.
    // `val = Σ_y Σ_x sel_row[y]·sel_col[x]·board[y·n+x]` is hash/lookup-free, degree 3, and
    // SEMANTICS-PRESERVING: `sel_row`/`sel_col` are each a single-hot (Σ=1, Σ index-pinned),
    // so exactly one product term is 1 and the read is the genuine addressed cell.

    /// A row×column pair of one-hots over an `n`×`n` board: `sel_row` (n-wide, hot at
    /// `y_hot`, pinned to `y_head`) and `sel_col` (n-wide, hot at `x_hot`, pinned to
    /// `x_head`). 2n selectors instead of the n² of a flat one-hot. Addressing cell
    /// `(x,y)` is the product `sel_row[y]·sel_col[x]`.
    pub fn one_hot_rowcol(
        &mut self,
        tag: &str,
        n: usize,
        x_hot: usize,
        x_head: &Head,
        y_hot: usize,
        y_head: &Head,
    ) -> (Vec<usize>, Vec<usize>) {
        let sel_row = self.one_hot(&format!("{tag}_r"), n, y_hot, y_head);
        let sel_col = self.one_hot(&format!("{tag}_c"), n, x_hot, x_head);
        (sel_row, sel_col)
    }

    /// Random-access board read via a row×column one-hot pair: `value_col == board[y·n+x]`,
    /// where the row `y` is pinned to `y_head` and the column `x` to `x_head`. Degree 3
    /// (`sel_row·sel_col·board`). The n²-wide twin of [`Self::one_hot_read`], at 2n selectors.
    #[allow(clippy::too_many_arguments)]
    pub fn read_rowcol(
        &mut self,
        tag: &str,
        board_cols: &[usize],
        n: usize,
        x_hot: usize,
        x_head: &Head,
        y_hot: usize,
        y_head: &Head,
        value_col: usize,
    ) {
        let (sel_row, sel_col) = self.one_hot_rowcol(tag, n, x_hot, x_head, y_hot, y_head);
        // value - Σ_y Σ_x sel_row[y]·sel_col[x]·board[y·n+x] == 0.
        let mut rd = Head::lin(1, value_col);
        for y in 0..n {
            for x in 0..n {
                rd = rd.add_prod(-1, vec![sel_row[y], sel_col[x], board_cols[y * n + x]]);
            }
        }
        self.assert_zero(&rd);
    }

    /// A GATED row×column one-hot pair: each of `sel_row`/`sel_col` sums to `gate` (all
    /// zero when the gate is off), and when on one-hots at `y_head`/`x_head`. So the cell
    /// address `sel_row[y]·sel_col[x]` is zero everywhere when `gate == 0`, and the single
    /// addressed cell when `gate == 1`. The row×column twin of [`Self::one_hot_gated`].
    #[allow(clippy::too_many_arguments)]
    pub fn one_hot_rowcol_gated(
        &mut self,
        tag: &str,
        n: usize,
        gate_col: usize,
        x_hot: usize,
        x_head: &Head,
        y_hot: usize,
        y_head: &Head,
    ) -> (Vec<usize>, Vec<usize>) {
        let sel_row = self.one_hot_gated(&format!("{tag}_r"), n, gate_col, y_hot, y_head);
        let sel_col = self.one_hot_gated(&format!("{tag}_c"), n, gate_col, x_hot, x_head);
        (sel_row, sel_col)
    }

    /// Gated random-access read via a row×column one-hot pair: `value_col == board[y·n+x]`
    /// when `gate` is on, else `value_col == 0` (the OOB/wall convention — the gated
    /// selectors are all zero, so the sum vanishes). Degree 3. The row×column twin of
    /// [`Self::one_hot_read_gated`], at 2n selectors.
    #[allow(clippy::too_many_arguments)]
    pub fn read_rowcol_gated(
        &mut self,
        tag: &str,
        board_cols: &[usize],
        n: usize,
        gate_col: usize,
        x_hot: usize,
        x_head: &Head,
        y_hot: usize,
        y_head: &Head,
        value_col: usize,
    ) {
        let (sel_row, sel_col) =
            self.one_hot_rowcol_gated(tag, n, gate_col, x_hot, x_head, y_hot, y_head);
        // value - Σ_y Σ_x sel_row[y]·sel_col[x]·board[y·n+x] == 0 (the gated selectors zero
        // the whole sum when the gate is off, giving value == 0).
        let mut rd = Head::lin(1, value_col);
        for y in 0..n {
            for x in 0..n {
                rd = rd.add_prod(-1, vec![sel_row[y], sel_col[x], board_cols[y * n + x]]);
            }
        }
        self.assert_zero(&rd);
    }

    /// Ray-scan read reusing an already-proven row×column one-hot pair (`sel_row`/`sel_col`
    /// pinned to the auto position), shifted by a COMPILE-TIME cardinal step `(sx, sy)`:
    /// `value_col == board[(y+sy)·n + (x+sx)]` when `gate` is on and the shifted cell is in
    /// bounds, else `value_col == 0`. Allocates NO new selector columns — the row×column twin
    /// of [`Self::shifted_read_gated`]. The 2-D bounds check (both `x+sx` and `y+sy` in range)
    /// is exact (no flat-index row-wrap). Degree 4 (`gate·sel_row·sel_col·board`).
    #[allow(clippy::too_many_arguments)]
    pub fn shifted_read_rowcol_gated(
        &mut self,
        sel_row: &[usize],
        sel_col: &[usize],
        board_cols: &[usize],
        n: usize,
        gate_col: usize,
        sx: i128,
        sy: i128,
        value_col: usize,
    ) {
        let mut rd = Head::lin(1, value_col);
        for y in 0..n {
            let ty = y as i128 + sy;
            if ty < 0 || ty as usize >= n {
                continue;
            }
            for x in 0..n {
                let tx = x as i128 + sx;
                if tx < 0 || tx as usize >= n {
                    continue;
                }
                let idx = (ty as usize) * n + (tx as usize);
                rd = rd.add_prod(-1, vec![gate_col, sel_row[y], sel_col[x], board_cols[idx]]);
            }
        }
        self.assert_zero(&rd);
    }

    /// A fresh column pinned to the product of two columns (`out == a*b`).
    pub fn alloc_prod(&mut self, name: &str, a: usize, b: usize) -> usize {
        let v = (self.values[a] * self.values[b]).0 as i128;
        let out = self.alloc(name, ColumnKind::Value, v);
        self.assert_zero(&Head::lin(-1, out).add_prod(1, vec![a, b]));
        out
    }

    /// A Poseidon2 `Hash4to1` SITE: constrain `output_col == hash_4_to_1(inputs)`. The
    /// output column's witness value is NOT touched here (the caller pins it to the
    /// committed hash — the sealed-move commitment); the constraint recomputes the hash
    /// of the four INPUT columns and equates it. `cellprogram_to_descriptor2` lowers this
    /// to a `TID_P2` Poseidon2 chip lookup, so a program carrying it PROVES-FOLDS as a
    /// custom leaf (unlike the `Hash` fact-sponge, which the IR-v2 chip adapter refuses).
    pub fn push_hash4to1(&mut self, output_col: usize, inputs: [usize; 4]) {
        self.push(ConstraintExpr::Hash4to1 {
            output_col,
            input_cols: inputs,
        });
    }

    /// The honest `hash_4_to_1` of four columns' witness values — the host commitment a
    /// caller pins a commit column to (so `air_accepts` shadows the real chip hash).
    pub fn hash4to1_value(&self, inputs: [usize; 4]) -> BabyBear {
        dregg_circuit::poseidon2::hash_4_to_1(&[
            self.values[inputs[0]],
            self.values[inputs[1]],
            self.values[inputs[2]],
            self.values[inputs[3]],
        ])
    }

    /// A native 8-felt cap-tree node compression SITE: constrain `output_cols == cap_node8(left, right)`
    /// — the arity-16 `node8` Poseidon2 compression, ALL 8 output lanes bound. Lowers to exactly ONE
    /// `TID_P2` chip lookup with ZERO auxiliary lane columns (`custom_leaf_lowering`), so a program
    /// carrying it PROVES-FOLDS as a custom leaf while binding the FULL 8-felt (~124-bit) digest —
    /// unlike `Hash4to1` (a ~31-bit lane-0 squeeze paying 7 witness columns). The output columns'
    /// witness values are set by the caller (from [`Self::merkle_hash8_value`]); the constraint
    /// recomputes `cap_node8` of the two 8-felt inputs and equates all eight lanes.
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

    /// The honest `cap_node8(left, right)` 8-felt compression — the value a caller fills a
    /// node's output columns with (so `air_accepts` shadows the real node8 chip hash).
    pub fn merkle_hash8_value(&self, left: [usize; 8], right: [usize; 8]) -> [BabyBear; 8] {
        let l: [BabyBear; 8] = core::array::from_fn(|i| self.values[left[i]]);
        let r: [BabyBear; 8] = core::array::from_fn(|i| self.values[right[i]]);
        dregg_circuit::cap_root::cap_node8(l, r)
    }

    /// **THE BOARD-STATE ROOT.** Build a CONSTRAINED 8-felt Poseidon2 (`cap_node8`) Merkle root
    /// over `cell_cols` (each a single-felt board square). The `k` cells are packed into
    /// `ceil(k/8)` 8-felt leaves (zero-padded on the last), then folded pairwise by a binary
    /// tree of `MerkleHash8` (arity-16 node8) sites into ONE 8-felt root. Every site is a real
    /// `ConstraintExpr::MerkleHash8`, so the returned root columns are EQUALITY-CONSTRAINED to
    /// the exact board columns the transition gadget reads: a forged root has no satisfying
    /// witness (it would need a full-width node8 collision). The leaf felts ARE the board
    /// columns themselves — no new leaf columns — so the root commits to precisely the board
    /// the AIR proves `new == apply_turn(old, moves)` over. Returns the 8 root column indices,
    /// which the caller `bind_pi`s so the ~124-bit board commitment becomes a published,
    /// constrained descriptor public input.
    pub fn board_root8(&mut self, tag: &str, cell_cols: &[usize]) -> [usize; 8] {
        // A shared zero column for padding leaves / odd siblings.
        let zero = self.col_by_name("mh8_zero").unwrap_or_else(|| {
            let z = self.alloc("mh8_zero", ColumnKind::Value, 0);
            self.assert_zero(&Head::lin(1, z));
            z
        });
        // Pack cells into 8-felt leaves.
        let mut level: Vec<[usize; 8]> = Vec::new();
        let mut i = 0;
        while i < cell_cols.len() {
            let leaf: [usize; 8] = core::array::from_fn(|j| {
                if i + j < cell_cols.len() {
                    cell_cols[i + j]
                } else {
                    zero
                }
            });
            level.push(leaf);
            i += 8;
        }
        // A single leaf still commits through a node8 (with a zero sibling), so the root is
        // always a genuine compression rather than a bare copy.
        if level.len() == 1 {
            level.push([zero; 8]);
        }
        // Fold pairwise up to a single root.
        let mut round = 0usize;
        while level.len() > 1 {
            let mut next: Vec<[usize; 8]> = Vec::new();
            for (pidx, ch) in level.chunks(2).enumerate() {
                let left = ch[0];
                let right = if ch.len() == 2 { ch[1] } else { [zero; 8] };
                let out_val = self.merkle_hash8_value(left, right);
                let out_cols: [usize; 8] = core::array::from_fn(|j| {
                    self.alloc(
                        format!("{tag}_r{round}_n{pidx}_l{j}"),
                        ColumnKind::Value,
                        out_val[j].0 as i128,
                    )
                });
                self.push_merkle_hash8(out_cols, left, right);
                next.push(out_cols);
            }
            level = next;
            round += 1;
        }
        level[0]
    }

    /// Bind an existing column to a FRESH public input: append the column's witness value
    /// as the next PI and pin `col == pi[index]` with a `PiBinding` constraint. Returns the
    /// PI index. The sealed-move commit column rides a PI this way, so the committed hash is
    /// a published descriptor PI (and is bound into the leaf's exposed PI commitment).
    pub fn bind_pi(&mut self, col: usize) -> usize {
        let pi_index = self.pis.len();
        self.pis.push(self.values[col]);
        self.public_input_count = self.pis.len();
        self.push(ConstraintExpr::PiBinding { col, pi_index });
        pi_index
    }

    // -------- witness self-evaluation (the `air_accepts` shadow) --------

    /// Evaluate every emitted constraint over the single witness row; return the list
    /// of `(constraint_index, residual)` that do NOT vanish. Empty => the AIR accepts.
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
}
