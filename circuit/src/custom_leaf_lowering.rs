//! Lower a `CellProgram` to an IR-v2 [`EffectVmDescriptor2`] — the PROVER-FREE
//! half of the custom-leaf adapter (Fork X).
//!
//! This module carries ONLY the LOWERING: the `ConstraintExpr` → `VmConstraint2`
//! mapping (`cellprogram_to_descriptor2` / `lower_cellprogram`) plus the
//! copy-forward trace-fill plan (`ChainFill` / `fill_chain_columns`) a trace
//! producer applies. It lives on the verify floor so the turn executor's
//! Custom-VK VERIFY path can lower a `CellProgram` without linking the recursion
//! prover. The PROVE half (`prove_custom_leaf`,
//! `prove_custom_leaf_with_commitment`, the in-circuit PI-commitment expose)
//! stays in `dregg-circuit-prove::custom_leaf_adapter`, whose module docs carry
//! the full constraint-mapping table, the lane-witnessing / running-hash /
//! `TableFunction` design notes, and the precise blockers for the unmapped
//! constraint kinds. `dregg-circuit-prove::custom_leaf_adapter` re-exports
//! [`cellprogram_to_descriptor2`], so existing callers are unchanged.

use crate::cap_root::CAP_FACT_MARK;
use crate::descriptor_ir2::{
    CHIP_OUT_LANES, CHIP_RATE, CHIP_TUPLE_LEN, EffectVmDescriptor2, LookupSpec, TID_P2,
    VmConstraint2, WindowExpr, WindowGateSpec,
};
use crate::dsl::circuit::{BoundaryDef, BoundaryRow, CellProgram, ConstraintExpr};
use crate::field::{BABYBEAR_P, BabyBear};
use crate::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};
use std::collections::HashMap;

/// `x − y` as a `LeanExpr` (no subtraction node: `x + (−1)·y`).
fn sub(x: LeanExpr, y: LeanExpr) -> LeanExpr {
    LeanExpr::add(x, LeanExpr::mul(LeanExpr::Const(-1), y))
}

/// Lower a PURE-LOCAL `ConstraintExpr` to the `LeanExpr` polynomial body that must
/// vanish (`body == 0`). Returns `Err` for any kind that is cross-row, PI-reading,
/// or otherwise not expressible as a single local gate body (those are handled — or
/// refused — at the top level in [`cellprogram_to_descriptor2`]).
fn gate_body(expr: &ConstraintExpr) -> Result<LeanExpr, String> {
    Ok(match expr {
        ConstraintExpr::Equality { col_a, col_b } => {
            sub(LeanExpr::Var(*col_a), LeanExpr::Var(*col_b))
        }
        ConstraintExpr::Multiplication { a, b, output } => sub(
            LeanExpr::mul(LeanExpr::Var(*a), LeanExpr::Var(*b)),
            LeanExpr::Var(*output),
        ),
        ConstraintExpr::Binary { col } => LeanExpr::mul(
            LeanExpr::Var(*col),
            LeanExpr::add(LeanExpr::Var(*col), LeanExpr::Const(-1)),
        ),
        ConstraintExpr::Polynomial { terms } => {
            // Σ coeffᵢ · ∏ colⱼ. The BabyBear coeff is carried as its canonical u32
            // value (< p) reduced back into the field at eval-time, so e.g. `p − 1`
            // is the faithful `−1`.
            let mut acc: Option<LeanExpr> = None;
            for term in terms {
                let mut prod = LeanExpr::Const(term.coeff.0 as i64);
                for &ci in &term.col_indices {
                    prod = LeanExpr::mul(prod, LeanExpr::Var(ci));
                }
                acc = Some(match acc {
                    None => prod,
                    Some(a) => LeanExpr::add(a, prod),
                });
            }
            // An empty polynomial is the zero constraint.
            acc.unwrap_or(LeanExpr::Const(0))
        }
        ConstraintExpr::Gated {
            selector_col,
            inner,
        } => LeanExpr::mul(LeanExpr::Var(*selector_col), gate_body(inner)?),
        ConstraintExpr::InvertedGated {
            selector_col,
            inner,
        } => LeanExpr::mul(
            sub(LeanExpr::Const(1), LeanExpr::Var(*selector_col)),
            gate_body(inner)?,
        ),
        ConstraintExpr::Squared { inner } => {
            let b = gate_body(inner)?;
            LeanExpr::mul(b.clone(), b)
        }
        ConstraintExpr::ConditionalNonzero {
            selector_col,
            value_col,
            inverse_col,
        } => LeanExpr::mul(
            LeanExpr::Var(*selector_col),
            sub(
                LeanExpr::mul(LeanExpr::Var(*value_col), LeanExpr::Var(*inverse_col)),
                LeanExpr::Const(1),
            ),
        ),
        ConstraintExpr::AtLeastOne { flag_cols } => {
            // ∏ (1 − flagᵢ) == 0 iff at least one flag is 1.
            let mut acc: Option<LeanExpr> = None;
            for &c in flag_cols {
                let factor = sub(LeanExpr::Const(1), LeanExpr::Var(c));
                acc = Some(match acc {
                    None => factor,
                    Some(a) => LeanExpr::mul(a, factor),
                });
            }
            // An empty AtLeastOne is unsatisfiable in the DSL evaluator (product of
            // no factors is 1, never 0); mirror that as the constant-1 gate.
            acc.unwrap_or(LeanExpr::Const(1))
        }
        // Cross-row / PI-reading / hash / lookup kinds are not local gate bodies.
        other => {
            return Err(format!(
                "constraint kind {} is not expressible as a local IR-v2 gate body",
                kind_name(other)
            ));
        }
    })
}

/// A short kind name for error messages.
fn kind_name(expr: &ConstraintExpr) -> &'static str {
    match expr {
        ConstraintExpr::Equality { .. } => "Equality",
        ConstraintExpr::Multiplication { .. } => "Multiplication",
        ConstraintExpr::Binary { .. } => "Binary",
        ConstraintExpr::PiBinding { .. } => "PiBinding",
        ConstraintExpr::Transition { .. } => "Transition",
        ConstraintExpr::Polynomial { .. } => "Polynomial",
        ConstraintExpr::Gated { .. } => "Gated",
        ConstraintExpr::InvertedGated { .. } => "InvertedGated",
        ConstraintExpr::Squared { .. } => "Squared",
        ConstraintExpr::Hash { .. } => "Hash",
        ConstraintExpr::ConditionalNonzero { .. } => "ConditionalNonzero",
        ConstraintExpr::AtLeastOne { .. } => "AtLeastOne",
        ConstraintExpr::Hash2to1 { .. } => "Hash2to1",
        ConstraintExpr::Hash4to1 { .. } => "Hash4to1",
        ConstraintExpr::Hash3Cap { .. } => "Hash3Cap",
        ConstraintExpr::MerkleHash8 { .. } => "MerkleHash8",
        ConstraintExpr::MerkleHash { .. } => "MerkleHash",
        ConstraintExpr::Lookup { .. } => "Lookup",
        ConstraintExpr::ChainedHash2to1 { .. } => "ChainedHash2to1",
        ConstraintExpr::SeedHash2to1 { .. } => "SeedHash2to1",
        ConstraintExpr::TableFunction { .. } => "TableFunction",
    }
}

// ============================================================================
// Poseidon2 lane-witnessing (the shared MerkleHash / TID_P2 extension).
//
// A `CellProgram` Poseidon2 hash site (`Hash2to1` / `Hash4to1` / `Hash3Cap` /
// `MerkleHash`) is ONE Poseidon2 permutation. The faithful IR-v2 carrier is a
// `Lookup` into the declared chip table `TID_P2`, whose row is the 20-wide tuple
// `[arity, in0..in10 (CHIP_RATE), out0, lane1..lane7]`. The chip-table AIR enforces
// `out[i] == perm(ins)[i]` for ALL 8 output lanes, so a forged digest OR a forged
// intermediate lane is UNSAT (`ir2_forged_output_lane_refuses`). The lookup balances
// (LogUp) the main-side send against that genuine chip row, so the recompute is
// witnessed by a pure light client folding the leaf — exactly the cap_root/heap_root
// in-circuit Merkle-open pattern (a witnessed sibling path, constrained recompute).
//
// `out0` is the site's own DIGEST column (the `CellProgram` already fills it via
// `generate_trace`); the 7 lane columns (lanes 1..7) are ALLOCATED past the base
// trace width and filled descriptor-side by `fill_chip_lanes` (the
// `trace_with_chip_lanes` weld inside `prove_vm_descriptor2_for_config`). A Merkle
// PATH is many such sites chained: each level's parent (`out0`) feeds the next level's
// `current` via a `Transition`, and the leaf/root are pinned to PIs by the boundary
// `PiBinding`s — so a wrong sibling no longer reaches the root PI and the leaf is UNSAT.
// ============================================================================

/// Build one `TID_P2` chip lookup for a single Poseidon2 permutation site.
///
/// `arity` selects the chip's state seeding (2 = `hash_2_to_1`, 3 = `cap_node`
/// `[FACT_MARK,l,r]`, 4 = `hash_4_to_1`), `ins` are the absorb input expressions
/// (zero-padded to `CHIP_RATE`), `out0_col` is the digest column the program fills,
/// and `lane_base..lane_base+6` are the 7 freshly-allocated lane columns (lanes 1..7).
/// The resulting 20-wide tuple matches the chip-row shape `MainLayout::build` validates.
fn chip_lookup_site(
    arity: u32,
    ins: &[LeanExpr],
    out0_col: usize,
    lane_base: usize,
) -> VmConstraint2 {
    let mut tuple: Vec<LeanExpr> = Vec::with_capacity(CHIP_TUPLE_LEN);
    tuple.push(LeanExpr::Const(arity as i64));
    for i in 0..CHIP_RATE {
        tuple.push(ins.get(i).cloned().unwrap_or(LeanExpr::Const(0)));
    }
    // out0 = the digest (lane 0); the AIR binds it to `perm(ins)[0]`.
    tuple.push(LeanExpr::Var(out0_col));
    // lanes 1..7 — the genuine distinct permutation lanes, witnessed columns the AIR
    // EQUALITY-binds to `perm(ins)[i]` (a forged lane is UNSAT). `fill_chip_lanes` writes them.
    for j in 0..(CHIP_OUT_LANES - 1) {
        tuple.push(LeanExpr::Var(lane_base + j));
    }
    debug_assert_eq!(tuple.len(), CHIP_TUPLE_LEN);
    VmConstraint2::Lookup(LookupSpec {
        table: TID_P2,
        tuple,
    })
}

/// The Lagrange leading coefficient `1 / ∏_{j≠i}(i − j)` of the degree-3 indicator
/// `ind_i(p)` over the 4-point grid `{0,1,2,3}` (so `ind_i(i) = 1`, `ind_i(j≠i) = 0`),
/// as a canonical BabyBear value. Used to express the position-dependent child
/// reconstruction of `MerkleHash` as `LeanExpr` chip-input polynomials.
fn lagrange_coeff(i: usize) -> BabyBear {
    let mut denom = BabyBear::ONE;
    for j in 0..4usize {
        if j != i {
            // (i − j) in the field (i, j ∈ 0..4 so the difference is small; lift via i64).
            let d = i64_to_field(i as i64 - j as i64);
            denom *= d;
        }
    }
    denom
        .inverse()
        .expect("Lagrange denominator over a 4-point grid is a unit")
}

/// `n` (possibly negative, small) as a canonical BabyBear.
fn i64_to_field(n: i64) -> BabyBear {
    let p = BABYBEAR_P as i64;
    let r = ((n % p) + p) % p;
    BabyBear::new(r as u32)
}

/// The degree-3 position indicator `ind_i(position_col)` as a `LeanExpr`:
/// `coeff_i · ∏_{j≠i}(position − j)`, which is `1` when `position == i` and `0` for the
/// other grid points `{0,1,2,3}` (pinned by the program's position-validity gate).
fn position_indicator(position_col: usize, i: usize) -> LeanExpr {
    let mut acc = LeanExpr::Const(lagrange_coeff(i).as_u32() as i64);
    for j in 0..4usize {
        if j != i {
            // (position − j)
            let factor = LeanExpr::add(LeanExpr::Var(position_col), LeanExpr::Const(-(j as i64)));
            acc = LeanExpr::mul(acc, factor);
        }
    }
    acc
}

/// Sum a list of `LeanExpr`s (empty = `Const(0)`).
fn add_all(terms: Vec<LeanExpr>) -> LeanExpr {
    let mut it = terms.into_iter();
    match it.next() {
        None => LeanExpr::Const(0),
        Some(first) => it.fold(first, LeanExpr::add),
    }
}

/// The four `MerkleHash` children as `LeanExpr`s over `(current, sib0, sib1, sib2,
/// position)`, reproducing the evaluator's reconstruction (`current` at slot
/// `position`, siblings filling the other slots IN ORDER) for every grid position
/// `{0,1,2,3}`. Each child is `ind_p·current + Σ [slot-belongs-to-sib_k]·sib_k`, a
/// degree-4 polynomial; off-grid points are irrelevant (the LogUp balances over trace
/// rows, where the position-validity gate pins `position ∈ {0,1,2,3}`).
fn merkle_children_exprs(
    current_col: usize,
    sib_cols: &[usize; 3],
    position_col: usize,
) -> [LeanExpr; 4] {
    let ind = |i: usize| position_indicator(position_col, i);
    let cur = || LeanExpr::Var(current_col);
    let sib = |k: usize| LeanExpr::Var(sib_cols[k]);
    let mul = LeanExpr::mul;
    // slot 0: current at p=0, else sib0 (the first non-position slot for p>0).
    let child0 = add_all(vec![
        mul(ind(0), cur()),
        mul(add_all(vec![ind(1), ind(2), ind(3)]), sib(0)),
    ]);
    // slot 1: current at p=1; sib0 at p=0; sib1 at p∈{2,3}.
    let child1 = add_all(vec![
        mul(ind(1), cur()),
        mul(ind(0), sib(0)),
        mul(add_all(vec![ind(2), ind(3)]), sib(1)),
    ]);
    // slot 2: current at p=2; sib1 at p∈{0,1}; sib2 at p=3.
    let child2 = add_all(vec![
        mul(ind(2), cur()),
        mul(add_all(vec![ind(0), ind(1)]), sib(1)),
        mul(ind(3), sib(2)),
    ]);
    // slot 3: current at p=3, else sib2 (the last non-position slot for p<3).
    let child3 = add_all(vec![
        mul(ind(3), cur()),
        mul(add_all(vec![ind(0), ind(1), ind(2)]), sib(2)),
    ]);
    [child0, child1, child2, child3]
}

// ============================================================================
// Bivariate Lagrange (the `TableFunction` GAP-A transition table → a local gate).
//
// `TableFunction { a, b, out, a_values, b_values, outputs }` asserts `out == P(a, b)`
// where `P` is the unique bivariate interpolant agreeing with `outputs` on the grid
// `a_values × b_values`. It is PURE-LOCAL and gate-expressible: lower it to the
// degree-`(|a|-1)+(|b|-1)` polynomial body `out − Σ_i Σ_j outputs[i·|b|+j]·Lᵢ(a)·Lⱼ(b)`,
// each `Lᵢ` a Lagrange indicator over the grid (`Lᵢ(grid_k) = δ_{ik}`), exactly as
// `MerkleHash`'s position reconstruction lowers its 4-point indicator. The paired
// grid-range vanishing gates (`∏ (col − v) == 0`) pin `(a, b)` onto the grid, so the
// interpolant is evaluated only at real grid points (off-grid escapes are impossible).
// ============================================================================

/// The Lagrange leading coefficient `1 / ∏_{k≠i}(values[i] − values[k])` over an
/// arbitrary distinct grid `values`, as a canonical BabyBear. `Err` if the grid has a
/// repeated value (a zero denominator — the descriptor's grid is distinct by construction).
fn grid_lagrange_coeff(values: &[u32], i: usize) -> Result<BabyBear, String> {
    let xi = i64_to_field(values[i] as i64);
    let mut denom = BabyBear::ONE;
    for (k, &vk) in values.iter().enumerate() {
        if k != i {
            denom *= xi - i64_to_field(vk as i64);
        }
    }
    denom.inverse().ok_or_else(|| {
        "TableFunction grid has a repeated value (Lagrange denominator 0)".to_string()
    })
}

/// The Lagrange indicator `Lᵢ(col)` over `values`: `coeff_i · ∏_{k≠i}(col − values[k])`,
/// which is `1` when `col == values[i]` and `0` at the other grid points (pinned by the
/// paired grid-range vanishing gate). A degree-`(|values|−1)` `LeanExpr`.
fn grid_indicator(col: usize, values: &[u32], i: usize) -> Result<LeanExpr, String> {
    let coeff = grid_lagrange_coeff(values, i)?;
    let mut acc = LeanExpr::Const(coeff.as_u32() as i64);
    for (k, &vk) in values.iter().enumerate() {
        if k != i {
            acc = LeanExpr::mul(
                acc,
                LeanExpr::add(LeanExpr::Var(col), LeanExpr::Const(-(vk as i64))),
            );
        }
    }
    Ok(acc)
}

/// Lower a `TableFunction` to its bivariate-interpolation gate body
/// `out − Σ_i Σ_j outputs[i·|b|+j]·Lᵢ(a)·Lⱼ(b)` (which must vanish).
fn table_function_body(
    a_col: usize,
    b_col: usize,
    out_col: usize,
    a_values: &[u32],
    b_values: &[u32],
    outputs: &[u32],
) -> Result<LeanExpr, String> {
    let nb = b_values.len();
    if outputs.len() != a_values.len() * nb {
        return Err(format!(
            "TableFunction outputs len {} != |a|·|b| {}",
            outputs.len(),
            a_values.len() * nb
        ));
    }
    let mut terms: Vec<LeanExpr> = Vec::with_capacity(outputs.len());
    for (i, _) in a_values.iter().enumerate() {
        let la = grid_indicator(a_col, a_values, i)?;
        for (j, _) in b_values.iter().enumerate() {
            let out_ij = outputs[i * nb + j];
            let lb = grid_indicator(b_col, b_values, j)?;
            terms.push(LeanExpr::mul(
                LeanExpr::mul(LeanExpr::Const(out_ij as i64), la.clone()),
                lb,
            ));
        }
    }
    // `out − P(a, b)`.
    Ok(sub(LeanExpr::Var(out_col), add_all(terms)))
}

// ============================================================================
// Running-hash chains (the cross-row `ChainedHash2to1` + its `SeedHash2to1` seed)
// lowered via a COPY-FORWARD accumulator column.
//
// A `CellProgram` `ChainedHash2to1 { out, seed, input }` is a CROSS-ROW relation
// `next[out] == hash_2_to_1(local[seed], next[input])`: the absorb seeds from the
// PREVIOUS row's accumulator. A single-row `TID_P2` chip lookup reads only the `local`
// window, so it cannot reach the `next` input. The faithful carrier is a fresh
// COPY-FORWARD witness column `acc` that carries the prior accumulator onto the current
// row, so the per-row chip is single-row again:
//
//   * per-row chip (every row j):  `out[j] == hash_2_to_1(acc[j], input[j])`   (TID_P2)
//   * copy-forward (transition):   `next[acc] − local[seed] == 0`              (WindowGate)
//   * seed pin (first row):        `acc[0] == pi[seed_pi_index]`               (PiBinding)
//
// The copy-forward sets `acc[i+1] = seed[i]` (= the previous accumulator), so the chip
// reproduces `out[i+1] = hash(seed[i], input[i+1])` byte-for-byte; row 0 is pinned by the
// `SeedHash2to1` seed (`acc[0] = pi[tableCommitment]`), reproducing `out[0] =
// hash(tableCommitment, input[0])`. Together they reproduce BOTH the `ChainedHash2to1`
// rolling step (C3) AND the `SeedHash2to1` seed of `dregg-dfa-routing-v1` exactly. The
// `acc` column is witnessed descriptor-side ([`fill_chain_columns`]); the chip equality-
// binds `out` to the genuine permutation, so a forged accumulator / broken chain is UNSAT.
// ============================================================================

/// The trace-fill plan for one running-hash chain: which fresh column carries the
/// copy-forward accumulator, which column it copies (`acc[i] = source[i−1]`), and the
/// first-row seed (`acc[0] = pi[seed_pi]`).
#[derive(Clone, Debug)]
pub struct ChainFill {
    /// The freshly-allocated copy-forward accumulator column.
    acc_col: usize,
    /// The source accumulator column copied forward (`acc[i] = source[i−1]`); the
    /// `ChainedHash2to1`'s `seed_local_col`.
    source_col: usize,
    /// The first-row seed public input (`acc[0] = pi[seed_pi]`).
    seed_pi: usize,
}

/// The result of lowering a `CellProgram`: the IR-v2 descriptor plus the copy-forward
/// fill plans the trace producer must apply ([`fill_chain_columns`]).
pub struct Lowered {
    pub desc: EffectVmDescriptor2,
    pub chains: Vec<ChainFill>,
}

/// Unwrap a (possibly `Gated`-wrapped) `SeedHash2to1`, returning `(output_col,
/// seed_pi_index, input_col)`. The `dregg-dfa-routing-v1` seed is `Gated { is_first,
/// SeedHash2to1 { .. } }`; the first-row PI-binding tag replaces the `is_first` gate, so
/// the gate selector is irrelevant here.
fn as_seed_hash(expr: &ConstraintExpr) -> Option<(usize, usize, usize)> {
    match expr {
        ConstraintExpr::SeedHash2to1 {
            output_col,
            seed_pi_index,
            input_col,
        } => Some((*output_col, *seed_pi_index, *input_col)),
        ConstraintExpr::Gated { inner, .. } => match &**inner {
            ConstraintExpr::SeedHash2to1 {
                output_col,
                seed_pi_index,
                input_col,
            } => Some((*output_col, *seed_pi_index, *input_col)),
            _ => None,
        },
        _ => None,
    }
}

/// Fill the copy-forward accumulator columns of `trace` (in place) per the lowered
/// chain plan, BEFORE the chip-lane weld runs: row 0 = the seed public input, row `i` =
/// the previous row's accumulator source. The chip-lane fill then derives each row's
/// genuine permutation lanes from this `acc` value, so `out == hash_2_to_1(acc, input)`
/// holds at every row.
pub fn fill_chain_columns(
    chains: &[ChainFill],
    trace: &mut [Vec<BabyBear>],
    public_inputs: &[BabyBear],
) {
    let n = trace.len();
    for chain in chains {
        if n == 0 {
            continue;
        }
        trace[0][chain.acc_col] = public_inputs
            .get(chain.seed_pi)
            .copied()
            .unwrap_or(BabyBear::ZERO);
        for i in 1..n {
            trace[i][chain.acc_col] = trace[i - 1][chain.source_col];
        }
    }
}

/// Adapt a `CellProgram`'s [`CircuitDescriptor`] into the IR-v2
/// [`EffectVmDescriptor2`] so it can prove through the general prover.
///
/// Each `ConstraintExpr` maps per the module-level table. The Poseidon2 hash kinds
/// `Hash2to1` / `Hash4to1` / `Hash3Cap` / `MerkleHash` lower to `TID_P2` chip lookups
/// with per-site lane columns allocated past the base trace width (the lane-witnessing
/// extension). The cross-row running hash `ChainedHash2to1` + its `SeedHash2to1` first-row
/// seed lower TOGETHER via a copy-forward accumulator column (a per-row chip + a
/// `WindowGate` copy-forward + a first-row PI pin — see the running-hash section). The
/// `TableFunction` lowers to its bivariate-Lagrange gate body. The remaining kinds
/// (`Hash` fact-sponge, arbitrary-entry `Lookup`, an UNSEEDED `ChainedHash2to1`, a
/// `SeedHash2to1` with no paired chain) have no faithful carrier here and are REFUSED with
/// a precise blocker. `BoundaryDef::PiBinding`/`Fixed` (first/last row) graduate to the
/// row-tagged IR-v2 boundary carriers, so a chained Merkle path's leaf/root pins survive.
pub fn cellprogram_to_descriptor2(program: &CellProgram) -> Result<EffectVmDescriptor2, String> {
    lower_cellprogram(program).map(|l| l.desc)
}

/// [`cellprogram_to_descriptor2`] plus the copy-forward fill plan ([`fill_chain_columns`])
/// the trace producer must apply. The public adapter discards the plan; the leaf provers
/// ([`prove_custom_leaf`] / [`prove_custom_leaf_with_commitment`]) use it to witness the
/// running-hash accumulator columns.
pub fn lower_cellprogram(program: &CellProgram) -> Result<Lowered, String> {
    let desc = &program.descriptor;
    let mut constraints: Vec<VmConstraint2> = Vec::with_capacity(desc.constraints.len());

    // Chip-lane columns are appended PAST the base trace width: each Poseidon2 site
    // claims `CHIP_OUT_LANES - 1` (= 7) fresh witnessed columns (lanes 1..7), filled
    // descriptor-side by `fill_chip_lanes`. The digest (lane 0/out0) is the site's own
    // output column (in-bounds, filled by `generate_trace`).
    let mut width = desc.trace_width;
    let alloc_lanes = |w: &mut usize| -> usize {
        let base = *w;
        *w += CHIP_OUT_LANES - 1;
        base
    };

    // Pre-pass: index the running-hash chain SEEDS. Each `(possibly-Gated) SeedHash2to1`
    // seeding a chain output column is consumed BY that chain (lowered as the chain's
    // first-row `acc[0] == pi[seed]` pin), so the main loop must SKIP it rather than try to
    // lower it as a standalone gate. A `SeedHash2to1` whose output column NO chain
    // accumulates is left unconsumed and hits the standalone-seed blocker below.
    let chain_outputs: std::collections::HashSet<usize> = desc
        .constraints
        .iter()
        .filter_map(|c| match c {
            ConstraintExpr::ChainedHash2to1 {
                output_next_col, ..
            } => Some(*output_next_col),
            _ => None,
        })
        .collect();
    // output_col -> (seed_pi_index, input_col), only for seeds a chain accumulates.
    let mut seed_of: HashMap<usize, (usize, usize)> = HashMap::new();
    let mut consumed_seed: Vec<bool> = vec![false; desc.constraints.len()];
    for (idx, c) in desc.constraints.iter().enumerate() {
        if let Some((out, pi, input)) = as_seed_hash(c)
            && chain_outputs.contains(&out)
        {
            seed_of.insert(out, (pi, input));
            consumed_seed[idx] = true;
        }
    }

    // The copy-forward fill plans accumulated as chains are lowered.
    let mut chains: Vec<ChainFill> = Vec::new();

    for (idx, expr) in desc.constraints.iter().enumerate() {
        // A `SeedHash2to1` consumed by its chain is lowered as that chain's first-row pin.
        if consumed_seed[idx] {
            continue;
        }
        let c2 = match expr {
            ConstraintExpr::PiBinding { col, pi_index } => {
                // A per-row PI gate is inexpressible in `LeanExpr`; the faithful
                // IR-v2 carrier is the row-tag-guarded `PiBinding`. This NARROWS the
                // CellProgram's every-row semantics to first-row (see module docs).
                VmConstraint2::Base(VmConstraint::PiBinding {
                    row: VmRow::First,
                    col: *col,
                    pi_index: *pi_index,
                })
            }
            ConstraintExpr::Transition {
                next_col,
                local_col,
            } => {
                // The two-row carrier: `next[next_col] − local[local_col] == 0` on
                // the transition domain (rows 0..n−2), faithful and column-general.
                VmConstraint2::WindowGate(WindowGateSpec {
                    body: WindowExpr::Add(
                        Box::new(WindowExpr::Nxt(*next_col)),
                        Box::new(WindowExpr::Mul(
                            Box::new(WindowExpr::Const(-1)),
                            Box::new(WindowExpr::Loc(*local_col)),
                        )),
                    ),
                    on_transition: true,
                })
            }
            // ---- Poseidon2 hash sites → TID_P2 chip lookups (the lane-witnessing weld) ----
            ConstraintExpr::Hash2to1 {
                output_col,
                input_col_a,
                input_col_b,
            } => {
                let lane_base = alloc_lanes(&mut width);
                chip_lookup_site(
                    2,
                    &[LeanExpr::Var(*input_col_a), LeanExpr::Var(*input_col_b)],
                    *output_col,
                    lane_base,
                )
            }
            ConstraintExpr::Hash4to1 {
                output_col,
                input_cols,
            } => {
                let lane_base = alloc_lanes(&mut width);
                chip_lookup_site(
                    4,
                    &input_cols
                        .iter()
                        .map(|&c| LeanExpr::Var(c))
                        .collect::<Vec<_>>(),
                    *output_col,
                    lane_base,
                )
            }
            ConstraintExpr::Hash3Cap {
                output_col,
                left_col,
                right_col,
            } => {
                // The cap-tree node hash `cap_node(l, r) = absorb([FACT_MARK, l, r])`
                // (arity-3 chip seeding), matching `cap_root::cap_node`.
                let lane_base = alloc_lanes(&mut width);
                chip_lookup_site(
                    3,
                    &[
                        LeanExpr::Const(CAP_FACT_MARK as i64),
                        LeanExpr::Var(*left_col),
                        LeanExpr::Var(*right_col),
                    ],
                    *output_col,
                    lane_base,
                )
            }
            ConstraintExpr::MerkleHash {
                output_col,
                current_col,
                sib_cols,
                position_col,
            } => {
                // The 4-ary parent hash: reconstruct the position-ordered children as
                // chip-input polynomials, then an arity-4 absorb (== `hash_4_to_1`).
                let lane_base = alloc_lanes(&mut width);
                let children = merkle_children_exprs(*current_col, sib_cols, *position_col);
                chip_lookup_site(4, &children, *output_col, lane_base)
            }
            // The native 8-felt cap-tree node8 compression is a MULTI-output (8-lane)
            // Poseidon2 site arithmetized only by the DSL batch-stark AIR (`dsl_p3_air`,
            // via `poseidon2_permute_expr_lanes`). This IR-v2 chip adapter carries
            // single-output (out0) chip sites, so it has no faithful carrier for the
            // 8-output node8 — a precise blocker, never a lane-0 downgrade.
            ConstraintExpr::MerkleHash8 { .. } => {
                return Err(
                    "constraint kind MerkleHash8 (native 8-felt cap_node8, arity-16 compression) \
                     is an 8-OUTPUT Poseidon2 site; this IR-v2 chip adapter carries single-output \
                     (out0) chip sites only. It is arithmetized by the DSL batch-stark AIR \
                     (dsl_p3_air, 8-lane exposure), not folded here"
                        .to_string(),
                );
            }
            // ---- the remaining hash / lookup / table-function kinds: no faithful
            //      single-permutation chip carrier in this extension — precise blockers. ----
            ConstraintExpr::Hash { .. } => {
                return Err(
                    "constraint kind Hash (capacity-tagged fact-sponge `hash_fact`) uses the \
                     arity-7 cap-leaf / FACT_MARK fact-bus seeding, NOT a narrow arity \
                     2/3/4 absorb; map it via the fact-bus chip path (the named follow-up)"
                        .to_string(),
                );
            }
            // ---- the cross-row running hash + its first-row seed → a copy-forward
            //      accumulator column (the per-row chip + WindowGate copy-forward + PI pin). ----
            ConstraintExpr::ChainedHash2to1 {
                output_next_col,
                seed_local_col,
                input_next_col,
            } => {
                // The chain is faithful ONLY with a paired first-row `SeedHash2to1` pinning
                // `acc[0]`: without it the per-row chip would over-constrain row 0 (`out[0] ==
                // hash(acc[0], input[0])`) where the bare chain leaves it free. An unseeded
                // ChainedHash2to1 is the precise named residual.
                let &(seed_pi, seed_input) = seed_of.get(output_next_col).ok_or_else(|| {
                    "constraint kind ChainedHash2to1 has no paired first-row SeedHash2to1 seed \
                     for its output column; the copy-forward carrier needs the seed to pin \
                     acc[0] (an UNSEEDED running hash is the named residual)"
                        .to_string()
                })?;
                if seed_input != *input_next_col {
                    return Err(format!(
                        "ChainedHash2to1 absorbs column {input_next_col} but its paired \
                         SeedHash2to1 absorbs column {seed_input}; the seed must absorb the \
                         same first-entry column the chain rolls"
                    ));
                }
                // A fresh copy-forward accumulator column `acc`, then its 7 chip lanes.
                let acc_col = width;
                width += 1;
                let lane_base = alloc_lanes(&mut width);
                // Copy-forward: `next[acc] − local[seed_local_col] == 0` (acc[i+1] = the prior
                // accumulator), the cross-row carrier the single-row chip cannot reach.
                constraints.push(VmConstraint2::WindowGate(WindowGateSpec {
                    body: WindowExpr::Add(
                        Box::new(WindowExpr::Nxt(acc_col)),
                        Box::new(WindowExpr::Mul(
                            Box::new(WindowExpr::Const(-1)),
                            Box::new(WindowExpr::Loc(*seed_local_col)),
                        )),
                    ),
                    on_transition: true,
                }));
                // First-row seed pin: `acc[0] == pi[seed_pi]` (the table-commitment seed).
                constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
                    row: VmRow::First,
                    col: acc_col,
                    pi_index: seed_pi,
                }));
                chains.push(ChainFill {
                    acc_col,
                    source_col: *seed_local_col,
                    seed_pi,
                });
                // The per-row chip: `out == hash_2_to_1(acc, input)` (single-row, arity 2).
                chip_lookup_site(
                    2,
                    &[LeanExpr::Var(acc_col), LeanExpr::Var(*input_next_col)],
                    *output_next_col,
                    lane_base,
                )
            }
            // A `SeedHash2to1` that reaches here is NOT consumed by a chain (no chain
            // accumulates its output column) — a standalone first-row PI-seeded hash, which
            // would need a first-row-ONLY chip gate (the named residual).
            ConstraintExpr::SeedHash2to1 { output_col, .. } => {
                return Err(format!(
                    "constraint kind SeedHash2to1 (output col {output_col}) is a standalone \
                     PUBLIC-INPUT-seeded first-row hash with no paired ChainedHash2to1 chain; a \
                     first-row-only chip gate is the named residual"
                ));
            }
            ConstraintExpr::Lookup { table_id, .. } => {
                return Err(format!(
                    "constraint kind Lookup(table \"{table_id}\") names an arbitrary \
                     CellProgram entry-set; IR-v2 lookups target fixed-semantics \
                     declared tables only — no faithful target in this extension"
                ));
            }
            // ---- the deterministic transition table → its bivariate-Lagrange gate body. ----
            ConstraintExpr::TableFunction {
                a_col,
                b_col,
                out_col,
                a_values,
                b_values,
                outputs,
            } => VmConstraint2::Base(VmConstraint::Gate(table_function_body(
                *a_col, *b_col, *out_col, a_values, b_values, outputs,
            )?)),
            // Everything else is a pure-local algebraic gate.
            local => VmConstraint2::Base(VmConstraint::Gate(gate_body(local)?)),
        };
        constraints.push(c2);
    }

    // Boundary pins (leaf/root for a Merkle path; any first/last cell binding) graduate
    // to the row-tagged IR-v2 boundary carriers. `BoundaryRow::Index` has no row-tag
    // carrier (`when_first_row`/`when_last_row` only), so it is refused.
    for b in &desc.boundaries {
        let vmrow = |row: &BoundaryRow| -> Result<VmRow, String> {
            match row {
                BoundaryRow::First => Ok(VmRow::First),
                BoundaryRow::Last => Ok(VmRow::Last),
                BoundaryRow::Index(i) => Err(format!(
                    "boundary at absolute row {i} has no IR-v2 row-tag carrier (only \
                     first/last are expressible)"
                )),
            }
        };
        let c2 = match b {
            BoundaryDef::PiBinding { row, col, pi_index } => {
                VmConstraint2::Base(VmConstraint::PiBinding {
                    row: vmrow(row)?,
                    col: *col,
                    pi_index: *pi_index,
                })
            }
            BoundaryDef::Fixed { row, col, value } => {
                // `local[col] − value == 0`, guarded by the row tag.
                VmConstraint2::Base(VmConstraint::Boundary {
                    row: vmrow(row)?,
                    body: sub(LeanExpr::Var(*col), LeanExpr::Const(value.as_u32() as i64)),
                })
            }
        };
        constraints.push(c2);
    }

    Ok(Lowered {
        desc: EffectVmDescriptor2 {
            name: format!("custom-leaf::{}", desc.name),
            trace_width: width,
            public_input_count: desc.public_input_count,
            tables: vec![],
            constraints,
            hash_sites: vec![],
            ranges: vec![],
        },
        chains,
    })
}
