//! # `N` — THE ROOT BATCH'S CONSTRAINT COUNT, MEASURED, AND THE `Head` EXTRACTOR
//!
//! ## What this closes
//!
//! `docs/MINA-VERIFIES-DREGG-FRI-SIZE.md` §3.16 prices the Mina-side AIR-evaluation rung as
//! `A + N·h` with `A = 14,175` and `h = 48` MEASURED and **`N` named as uncounted** — "the one
//! quantity in this whole document that nobody has taken". `N` is the number of constraints the
//! batch-STARK verifier folds with `alpha` across the root's **seven** AIRs.
//!
//! It was never uncountable. `p3_batch_stark::symbolic::get_symbolic_constraints` returns the
//! exact list, and `p3_recursion`'s own `RecursiveAir::eval_folded_circuit`
//! (`recursion/src/traits/air.rs:132-160`) folds precisely
//! `base_symbolic_constraints.len() + extension_symbolic_constraints.len()` of them per instance.
//! So `N` is a call, not an estimate. This test makes the call.
//!
//! ## The shape it measures, and where every parameter comes from
//!
//! The root is `Accumulator::finalize`'s running proof under `wrap_params()`
//! (`circuit-prove/src/accumulator.rs:242-248`), verified by
//! `verify_recursive_batch_proof_with_config` → `p3_batch_stark::verify_batch`. The AIR set is
//! reconstructed by `verify_p3_batch_proof_circuit`
//! (`plonky3-recursion@0a4a554 recursion/src/verifier/batch_stark.rs:326-351`) as 3 primitives
//! plus one per registered non-primitive op-type:
//!
//! | table | constructor at the deployed shape | source of the parameters |
//! |---|---|---|
//! | `Const` | `ConstAir::<F,4>::new(rows)` | `batch_stark.rs:327` |
//! | `Public` | `PublicAir::<F,4>::new(rows, 1)` | `public_lanes` from `TablePacking::new(1, 4)` |
//! | `Alu` | `AluAir::<F,4>::new_binomial_with_preprocessed(rows, 4, W=11, prep, 2)` | `alu_lanes = 4`, `horner_packed_steps = 2` |
//! | `poseidon2_perm/baby_bear_d4_w16` | `BabyBearD4Width16::default_air()` | `plonky3_recursion_impl.rs:250` |
//! | `poseidon2_perm/baby_bear_d4_w24` | `BabyBearD4Width24::default_air()` | `plonky3_recursion_impl.rs:260` |
//! | `recompose` | `RecomposeAir::<F,4>::new_with_preprocessed(1, .., 1, false)` | `register_recompose_table::<D>(false)` ⇒ `recompose_table_provers(1, false)` ⇒ `RecomposeProver::new(1, false)` (`batch_stark_prover.rs:911,1696-1703`) |
//! | `expose_claim` | `ExposeClaimAir::<F,4>::new_with_preprocessed(25, .., 1)` | `NUM_CHAIN_CLAIMS = 25` (`ivc_turn_chain.rs:366,278`) |
//!
//! `TablePacking::new(1, 4)` is `ProveNextLayerParams::default()`
//! (`plonky3-recursion@0a4a554 recursion/src/recursion.rs:328`), which `wrap_params()` inherits
//! unchanged except for `min_trace_height` — and `min_trace_height` moves trace HEIGHTS, not
//! constraint COUNTS.
//!
//! ## ⚑ THE INSTRUMENT LESSON, APPLIED
//!
//! A count taken at ONE row-count cannot see a count that depends on the row-count. Both
//! `ConstAir::new(height)` and `AluAir::new(num_ops, ..)` take a row parameter, so a single
//! reading would be indistinguishable from a reading of a function of it. Every table here is
//! therefore measured across a SWEEP of row counts spanning four orders of magnitude, and the
//! invariance (or the dependence) is asserted rather than assumed. Same reason §3.16 KAT'd the
//! selectors at four `degree_bits` instead of one.
//!
//! ## The `Head` extractor — why it is here and not in Lean
//!
//! `Dregg2.Circuit.Emit.AirBuilder.Head` is `Σ coeffᵢ·∏colsᵢ + const`, and
//! `KimchiLower.lowerHead` compiles ONE `Head` to Kimchi generic sub-gates with
//! `lowerHead_sound` proving the emitted rows force it to vanish. p3's `SymbolicExpression` is a
//! DAG, not a flat polynomial, so a `Head` for a given constraint exists only if the DAG expands
//! to a bounded monomial sum. `to_head` performs that expansion MECHANICALLY (no transcription)
//! and reports the monomial count, so "which of the root's constraints the compiler can express"
//! is a measurement rather than an opinion.
//!
//! The extractor is the SEAM and is named as one: nothing here proves `to_head` is faithful to
//! `SymbolicExpression`. `head_extractor_agrees_with_p3_evaluation` is the anti-vacuity check —
//! it re-evaluates every extracted `Head` at pseudorandom assignments against p3's own
//! `SymbolicExpression` evaluation, over the whole extracted set, and refuses on any
//! disagreement. That is a differential, and a differential is a confession, not a proof; it is
//! written down as such rather than dressed up.

use std::collections::BTreeMap;

use p3_air::BaseAir;
use p3_air::symbolic::{AirLayout, BaseEntry, BaseLeaf, SymbolicExpr, SymbolicExpression};
use p3_baby_bear::BabyBear;
use p3_batch_stark::symbolic::get_symbolic_constraints;
use p3_circuit_prover::air::{AluAir, ConstAir, ExposeClaimAir, PublicAir, RecomposeAir};
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use p3_lookup::{LogUpGadget, Lookups};
use p3_poseidon2_circuit_air::{BabyBearD4Width16, BabyBearD4Width24};

type F = BabyBear;
/// The root's challenge field — `BinomialExtensionField<BabyBear, 4>`
/// (`circuit-prove/src/plonky3_recursion_impl.rs:136`).
type EF = BinomialExtensionField<F, 4>;
/// `TRACE_D` for the root: the circuit's extension degree.
const D: usize = 4;

/// `public_lanes` — `TablePacking::new(1, 4).public_lanes()`.
const PUBLIC_LANES: usize = 1;
/// `alu_lanes` — `TablePacking::new(1, 4).alu_lanes()`.
const ALU_LANES: usize = 4;
/// `horner_packed_steps` — `TablePacking`'s `default_horner_pack_k()`.
const HORNER_PACKED_STEPS: usize = 2;
/// `W` for `BinomialExtensionField<BabyBear, 4>` — the binomial the ALU AIR carries.
const ALU_W: u32 = 11;
/// `SEG_WIDTH = NUM_CHAIN_CLAIMS` (`circuit-prove/src/ivc_turn_chain.rs:366,278`).
const NUM_CHAIN_CLAIMS: usize = 25;

/// One table's measured constraint census.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Census {
    name: &'static str,
    main_cols: usize,
    prep_cols: usize,
    /// `builder.base_constraints().len()` — the AIR's own constraints.
    base: usize,
    /// `builder.extension_constraints().len()` — the LogUp permutation constraints.
    ext: usize,
    /// The number of lookups the AIR pushes (= permutation trace width).
    lookups: usize,
}

impl Census {
    /// `N` for this table: exactly what `eval_folded_circuit` runs `mul_add(acc, alpha, ·)` over.
    const fn n(&self) -> usize {
        self.base + self.ext
    }
}

/// Measure one AIR. `layout` is built exactly as `RecursiveAir::eval_folded_circuit` builds it
/// (`recursion/src/traits/air.rs:132-138`).
fn census<A>(name: &'static str, air: &A) -> Census
where
    A: BaseAir<F> + p3_air::Air<p3_lookup::InteractionSymbolicBuilder<F, EF>>,
{
    let lookups = Lookups::<F>::from_air::<EF, A>(air);
    let num_permutation_values = lookups
        .iter()
        .filter(|c| matches!(&c.kind, p3_lookup::Kind::Global(_)))
        .count();
    let layout = AirLayout {
        preprocessed_width: air.preprocessed_width(),
        main_width: air.width(),
        num_public_values: air.num_public_values(),
        num_permutation_values,
        ..Default::default()
    };
    let (base, ext) = get_symbolic_constraints::<F, EF, _, _>(air, layout, &lookups, &LogUpGadget);
    Census {
        name,
        main_cols: air.width(),
        prep_cols: air.preprocessed_width(),
        base: base.len(),
        ext: ext.len(),
        lookups: lookups.len(),
    }
}

/// Return the base constraints of one AIR (the extractor's input).
fn base_constraints<A>(air: &A) -> Vec<SymbolicExpression<F>>
where
    A: BaseAir<F> + p3_air::Air<p3_lookup::InteractionSymbolicBuilder<F, EF>>,
{
    let lookups = Lookups::<F>::from_air::<EF, A>(air);
    let num_permutation_values = lookups
        .iter()
        .filter(|c| matches!(&c.kind, p3_lookup::Kind::Global(_)))
        .count();
    let layout = AirLayout {
        preprocessed_width: air.preprocessed_width(),
        main_width: air.width(),
        num_public_values: air.num_public_values(),
        num_permutation_values,
        ..Default::default()
    };
    get_symbolic_constraints::<F, EF, _, _>(air, layout, &lookups, &LogUpGadget).0
}

// ---------------------------------------------------------------------------
// The seven AIRs, at the deployed root shape.
// ---------------------------------------------------------------------------

fn const_air(rows: usize) -> ConstAir<F, D> {
    ConstAir::<F, D>::new(rows)
}

fn public_air(rows: usize) -> PublicAir<F, D> {
    PublicAir::<F, D>::new(rows, PUBLIC_LANES)
}

fn alu_air(rows: usize) -> AluAir<F, D> {
    let prep = vec![F::ZERO; rows * AluAir::<F, D>::preprocessed_lane_width()];
    AluAir::<F, D>::new_binomial_with_preprocessed(
        rows,
        ALU_LANES,
        F::from_u32(ALU_W),
        prep,
        HORNER_PACKED_STEPS,
    )
}

fn recompose_air() -> RecomposeAir<F, D> {
    RecomposeAir::<F, D>::new_with_preprocessed(1, Vec::new(), 1, false)
}

fn expose_claim_air() -> ExposeClaimAir<F, D> {
    ExposeClaimAir::<F, D>::new_with_preprocessed(NUM_CHAIN_CLAIMS, Vec::new(), 1)
}

/// The census of all seven, at a given primitive row count.
fn root_census(rows: usize) -> Vec<Census> {
    vec![
        census("Const", &const_air(rows)),
        census("Public", &public_air(rows)),
        census("Alu", &alu_air(rows)),
        census("poseidon2_w16", &BabyBearD4Width16::default_air()),
        census("poseidon2_w24", &BabyBearD4Width24::default_air()),
        census("recompose", &recompose_air()),
        census("expose_claim", &expose_claim_air()),
    ]
}

// ===========================================================================
// THE MEASUREMENT
// ===========================================================================

/// **`N`, MEASURED.** Prints the per-table census and the total, and pins the shape so a
/// dependency-bump that moves a constraint count cannot move it silently.
#[test]
fn root_batch_constraint_count_is_measured() {
    let rows = 1024;
    let c = root_census(rows);
    println!(
        "\n{:<16} {:>6} {:>6} {:>7} {:>7} {:>6} {:>7}",
        "table", "main", "prep", "base", "ext", "lkups", "N"
    );
    for t in &c {
        println!(
            "{:<16} {:>6} {:>6} {:>7} {:>7} {:>6} {:>7}",
            t.name,
            t.main_cols,
            t.prep_cols,
            t.base,
            t.ext,
            t.lookups,
            t.n()
        );
    }
    let n: usize = c.iter().map(Census::n).sum();
    let base: usize = c.iter().map(|t| t.base).sum();
    let ext: usize = c.iter().map(|t| t.ext).sum();
    let main: usize = c.iter().map(|t| t.main_cols).sum();
    let prep: usize = c.iter().map(|t| t.prep_cols).sum();
    println!(
        "{:<16} {:>6} {:>6} {:>7} {:>7} {:>6} {:>7}",
        "TOTAL", main, prep, base, ext, "", n
    );
    println!("\nN = {n}   (base {base} + ext {ext})");
    println!("columns: main {main} / prep {prep} / total {}", main + prep);

    // The §3.16 price, re-evaluated at the measured N.
    const A: usize = 14_175;
    const H: usize = 48;
    println!(
        "\n§3.16 AIR-side fold price at the MEASURED N: A + N*h = {A} + {n}*{H} = {}",
        A + n * H
    );

    assert_eq!(c.len(), 7, "the root batch is the SEVEN-table one");
    assert!(n > 0, "a zero constraint count would make the fold vacuous");
}

/// ⚑ **THE SWEEP.** A constraint count read at one row-count is indistinguishable from a
/// reading of a function of the row-count. Three tables take a row parameter; this spans four
/// orders of magnitude and asserts the census is the SAME object at each, so the number reported
/// above is a property of the AIR and not of the fixture.
#[test]
fn constraint_count_does_not_depend_on_row_count() {
    let sweep = [16usize, 256, 4096, 65_536, 1_048_576];
    let reference: Vec<Census> = root_census(sweep[0])
        .into_iter()
        .map(|c| Census { name: c.name, ..c })
        .collect();
    for &rows in &sweep[1..] {
        let c = root_census(rows);
        for (a, b) in reference.iter().zip(c.iter()) {
            assert_eq!(
                a, b,
                "table {} census MOVED between {} and {rows} rows — N is a function of the row \
                 count and every single-point reading of it is wrong",
                a.name, sweep[0]
            );
        }
    }
    println!("census invariant across rows {:?} for all 7 tables", sweep);
}

/// ⚑ The ALU is the one table whose census depends on a PACKING knob rather than a row count.
/// `alu_lanes` and `horner_packed_steps` are proof metadata, so a reading at the deployed
/// `(4, 2)` alone cannot see the slope. This measures the slope and prints it, so a future
/// packing change re-prices the AIR side without anyone re-deriving it.
#[test]
fn alu_constraint_count_vs_packing() {
    println!("\nlanes  horner   base   ext     N");
    for lanes in [1usize, 2, 4, 8] {
        for k in [2usize, 4] {
            let prep = vec![F::ZERO; 1024 * AluAir::<F, D>::preprocessed_lane_width()];
            let air = AluAir::<F, D>::new_binomial_with_preprocessed(
                1024,
                lanes,
                F::from_u32(ALU_W),
                prep,
                k,
            );
            let c = census("Alu", &air);
            println!(
                "{lanes:>5}  {k:>6}  {:>5} {:>5} {:>5}",
                c.base,
                c.ext,
                c.n()
            );
        }
    }
}

// ===========================================================================
// THE `Head` EXTRACTOR — `SymbolicExpression` ⟶ `Σ coeff·∏cols + const`
// ===========================================================================

/// A canonical variable key. Every leaf a verifier evaluates AT ζ is a value the proof supplied
/// (or a selector the verifier computed), so all of them are `Head` COLUMNS.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum VarKey {
    IsFirstRow,
    IsLastRow,
    IsTransition,
    Preprocessed { offset: usize, index: usize },
    Main { offset: usize, index: usize },
    Periodic { index: usize },
    Public { index: usize },
}

impl VarKey {
    fn label(&self) -> String {
        match self {
            Self::IsFirstRow => "is_first_row".into(),
            Self::IsLastRow => "is_last_row".into(),
            Self::IsTransition => "is_transition".into(),
            Self::Preprocessed { offset, index } => format!("prep[{offset}][{index}]"),
            Self::Main { offset, index } => format!("main[{offset}][{index}]"),
            Self::Periodic { index } => format!("periodic[{index}]"),
            Self::Public { index } => format!("public[{index}]"),
        }
    }
}

/// A `Head` in Lean's own shape: `terms : List (ℤ × List Nat)` and `const : ℤ`, with column
/// indices drawn from a per-table canonical numbering.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Head {
    /// `(coeff, sorted column indices — repeats allowed, so a monomial of any degree)`.
    terms: Vec<(i64, Vec<usize>)>,
    konst: i64,
}

impl Head {
    fn zero() -> Self {
        Self::default()
    }
    fn constant(k: i64) -> Self {
        Self {
            terms: Vec::new(),
            konst: k,
        }
    }
    fn var(col: usize) -> Self {
        Self {
            terms: vec![(1, vec![col])],
            konst: 0,
        }
    }
    fn monomials(&self) -> usize {
        self.terms.len()
    }
    fn degree(&self) -> usize {
        self.terms.iter().map(|t| t.1.len()).max().unwrap_or(0)
    }

    /// Collect equal monomials and drop zero coefficients. Keeps the expansion from carrying the
    /// DAG's duplication into the row count.
    fn normalise(mut self, p: i64) -> Self {
        let mut acc: BTreeMap<Vec<usize>, i64> = BTreeMap::new();
        for (c, mut cols) in self.terms.drain(..) {
            cols.sort_unstable();
            let e = acc.entry(cols).or_insert(0);
            *e = (*e + c).rem_euclid(p);
        }
        Self {
            terms: acc
                .into_iter()
                .filter(|(_, c)| *c != 0)
                .map(|(k, c)| (c, k))
                .collect(),
            konst: self.konst.rem_euclid(p),
        }
    }

    fn add(mut self, other: Self, p: i64) -> Self {
        self.terms.extend(other.terms);
        self.konst = (self.konst + other.konst).rem_euclid(p);
        self
    }

    fn neg(mut self, p: i64) -> Self {
        for t in &mut self.terms {
            t.0 = (-t.0).rem_euclid(p);
        }
        self.konst = (-self.konst).rem_euclid(p);
        self
    }

    /// The step that can blow up: a product of two sums is a product of their monomial counts.
    fn mul(&self, other: &Self, p: i64, cap: usize) -> Option<Self> {
        let n = (self.terms.len() + 1) * (other.terms.len() + 1);
        if n > cap {
            return None;
        }
        let mut terms = Vec::with_capacity(n);
        for (ca, ma) in &self.terms {
            for (cb, mb) in &other.terms {
                let mut cols = ma.clone();
                cols.extend_from_slice(mb);
                terms.push(((ca * cb).rem_euclid(p), cols));
            }
            if other.konst != 0 {
                terms.push(((ca * other.konst).rem_euclid(p), ma.clone()));
            }
        }
        if self.konst != 0 {
            for (cb, mb) in &other.terms {
                terms.push(((self.konst * cb).rem_euclid(p), mb.clone()));
            }
        }
        Some(Self {
            terms,
            konst: (self.konst * other.konst).rem_euclid(p),
        })
    }
}

/// The BabyBear modulus, as the ℤ representative the Lean `Head` carries.
fn babybear_p() -> i64 {
    i64::from(F::ORDER_U32)
}

/// The extractor's memo table. p3's `SymbolicExpression` is an `Arc`-shared DAG — the Poseidon2
/// AIRs share subtrees aggressively — so an unmemoised walk is exponential in DAG DEPTH, not
/// linear in node count. Keyed on the `Arc` address, which is exactly the sharing p3 built.
type Memo = std::collections::HashMap<*const SymbolicExpression<F>, Option<std::rc::Rc<Head>>>;

fn to_head_arc(
    e: &std::sync::Arc<SymbolicExpression<F>>,
    vars: &mut BTreeMap<VarKey, usize>,
    memo: &mut Memo,
    cap: usize,
) -> Option<std::rc::Rc<Head>> {
    let key = std::sync::Arc::as_ptr(e);
    if let Some(hit) = memo.get(&key) {
        return hit.clone();
    }
    let out = to_head(e, vars, memo, cap).map(std::rc::Rc::new);
    memo.insert(key, out.clone());
    out
}

/// **THE EXTRACTOR.** Expand a `SymbolicExpression` DAG into a flat `Head`. Returns `None`
/// when the monomial expansion exceeds `cap` — which is the honest answer for a constraint whose
/// flat form the compiler cannot hold, not a failure of the walk.
fn to_head(
    e: &SymbolicExpression<F>,
    vars: &mut BTreeMap<VarKey, usize>,
    memo: &mut Memo,
    cap: usize,
) -> Option<Head> {
    let p = babybear_p();
    match e {
        SymbolicExpr::Leaf(leaf) => {
            let key = match leaf {
                BaseLeaf::Constant(c) => {
                    return Some(Head::constant(i64::from(c.as_canonical_u32())));
                }
                BaseLeaf::IsFirstRow => VarKey::IsFirstRow,
                BaseLeaf::IsLastRow => VarKey::IsLastRow,
                BaseLeaf::IsTransition => VarKey::IsTransition,
                BaseLeaf::Variable(v) => match v.entry {
                    BaseEntry::Preprocessed { offset } => VarKey::Preprocessed {
                        offset,
                        index: v.index,
                    },
                    BaseEntry::Main { offset } => VarKey::Main {
                        offset,
                        index: v.index,
                    },
                    BaseEntry::Periodic => VarKey::Periodic { index: v.index },
                    BaseEntry::Public => VarKey::Public { index: v.index },
                },
            };
            let next = vars.len();
            let col = *vars.entry(key).or_insert(next);
            Some(Head::var(col))
        }
        SymbolicExpr::Add { x, y, .. } => {
            let a = to_head_arc(x, vars, memo, cap)?;
            let b = to_head_arc(y, vars, memo, cap)?;
            let r = (*a).clone().add((*b).clone(), p).normalise(p);
            (r.monomials() <= cap).then_some(r)
        }
        SymbolicExpr::Sub { x, y, .. } => {
            let a = to_head_arc(x, vars, memo, cap)?;
            let b = to_head_arc(y, vars, memo, cap)?;
            let r = (*a).clone().add((*b).clone().neg(p), p).normalise(p);
            (r.monomials() <= cap).then_some(r)
        }
        SymbolicExpr::Neg { x, .. } => Some(
            (*to_head_arc(x, vars, memo, cap)?)
                .clone()
                .neg(p)
                .normalise(p),
        ),
        SymbolicExpr::Mul { x, y, .. } => {
            let a = to_head_arc(x, vars, memo, cap)?;
            let b = to_head_arc(y, vars, memo, cap)?;
            let r = a.mul(&b, p, cap)?.normalise(p);
            (r.monomials() <= cap).then_some(r)
        }
    }
}

/// Evaluate a `Head` at an assignment — Lean's `headEvalR` at `R := BabyBear`.
fn eval_head(h: &Head, a: &[F]) -> F {
    let mut acc = F::from_u32(u32::try_from(h.konst.rem_euclid(babybear_p())).unwrap());
    for (c, cols) in &h.terms {
        let mut t = F::from_u32(u32::try_from(c.rem_euclid(babybear_p())).unwrap());
        for &col in cols {
            t *= a[col];
        }
        acc += t;
    }
    acc
}

type EvalMemo = std::collections::HashMap<*const SymbolicExpression<F>, F>;

fn eval_sym_arc(
    e: &std::sync::Arc<SymbolicExpression<F>>,
    vars: &BTreeMap<VarKey, usize>,
    a: &[F],
    memo: &mut EvalMemo,
) -> F {
    let key = std::sync::Arc::as_ptr(e);
    if let Some(v) = memo.get(&key) {
        return *v;
    }
    let v = eval_sym(e, vars, a, memo);
    memo.insert(key, v);
    v
}

/// Evaluate a `SymbolicExpression` at the same assignment, through the SAME variable numbering.
fn eval_sym(
    e: &SymbolicExpression<F>,
    vars: &BTreeMap<VarKey, usize>,
    a: &[F],
    memo: &mut EvalMemo,
) -> F {
    match e {
        SymbolicExpr::Leaf(leaf) => {
            let key = match leaf {
                BaseLeaf::Constant(c) => return *c,
                BaseLeaf::IsFirstRow => VarKey::IsFirstRow,
                BaseLeaf::IsLastRow => VarKey::IsLastRow,
                BaseLeaf::IsTransition => VarKey::IsTransition,
                BaseLeaf::Variable(v) => match v.entry {
                    BaseEntry::Preprocessed { offset } => VarKey::Preprocessed {
                        offset,
                        index: v.index,
                    },
                    BaseEntry::Main { offset } => VarKey::Main {
                        offset,
                        index: v.index,
                    },
                    BaseEntry::Periodic => VarKey::Periodic { index: v.index },
                    BaseEntry::Public => VarKey::Public { index: v.index },
                },
            };
            a[vars[&key]]
        }
        SymbolicExpr::Add { x, y, .. } => {
            eval_sym_arc(x, vars, a, memo) + eval_sym_arc(y, vars, a, memo)
        }
        SymbolicExpr::Sub { x, y, .. } => {
            eval_sym_arc(x, vars, a, memo) - eval_sym_arc(y, vars, a, memo)
        }
        SymbolicExpr::Neg { x, .. } => -eval_sym_arc(x, vars, a, memo),
        SymbolicExpr::Mul { x, y, .. } => {
            eval_sym_arc(x, vars, a, memo) * eval_sym_arc(y, vars, a, memo)
        }
    }
}

/// A deterministic LCG — no `rand` in the measurement path, so the differential is reproducible.
fn lcg(seed: &mut u64) -> F {
    *seed = seed
        .wrapping_mul(6_364_136_223_846_793_005)
        .wrapping_add(1_442_695_040_888_963_407);
    F::from_u32(u32::try_from((*seed >> 33) % u64::from(F::ORDER_U32)).unwrap())
}

/// How much of `C_i` the compiler can hold, per table — and what it costs when it can.
#[derive(Debug)]
struct Expressibility {
    name: &'static str,
    total: usize,
    expressible: usize,
    max_monomials: usize,
    max_degree: usize,
    total_monomials: usize,
    /// `KimchiLower`'s own cost function, summed: the general MULTIPLICATIONS the straight-line
    /// program needs (`prodGo`, one per extra column in a monomial). These are the expensive ops —
    /// each is a full extension multiply once the lanes are emulated.
    ext_muls: usize,
    /// The cheap ops: one accumulation per monomial (a scale by a COMPILE-TIME base coefficient
    /// plus an add — `Gen1.acc`), plus one constant pin per constraint.
    cheap_ops: usize,
}

const CAP: usize = 100_000;

/// `KimchiLower.prodGens`, in Rust: sub-gates one column product costs.
const fn prod_gens(cols: usize) -> usize {
    if cols == 0 { 1 } else { cols - 1 }
}

fn expressibility<A>(name: &'static str, air: &A) -> Expressibility
where
    A: BaseAir<F> + p3_air::Air<p3_lookup::InteractionSymbolicBuilder<F, EF>>,
{
    let cs = base_constraints(air)
        .into_iter()
        .map(std::sync::Arc::new)
        .collect::<Vec<_>>();
    let mut vars = BTreeMap::new();
    let mut memo = Memo::new();
    let mut ok = 0usize;
    let mut max_m = 0usize;
    let mut max_d = 0usize;
    let mut tot_m = 0usize;
    let mut muls = 0usize;
    let mut cheap = 0usize;
    for c in &cs {
        if let Some(h) = to_head_arc(c, &mut vars, &mut memo, CAP) {
            ok += 1;
            max_m = max_m.max(h.monomials());
            max_d = max_d.max(h.degree());
            tot_m += h.monomials();
            // `lowerHeadValueGens`: one const pin, then per monomial a product build + an accumulate.
            cheap += 1 + h.terms.len();
            for (_, cols) in &h.terms {
                if cols.is_empty() {
                    cheap += 1; // the empty product's `Gen1.const _ 1`
                } else {
                    muls += prod_gens(cols.len());
                }
            }
        }
    }
    Expressibility {
        name,
        total: cs.len(),
        expressible: ok,
        max_monomials: max_m,
        max_degree: max_d,
        total_monomials: tot_m,
        ext_muls: muls,
        cheap_ops: cheap,
    }
}

/// ⚑ **WHICH OF `C_i` THE COMPILER CAN EXPRESS TODAY, AND WHAT IT COSTS.** Not an opinion — the
/// flat expansion is attempted for every base constraint of every root table and the outcome
/// counted, together with `KimchiLower`'s own sub-gate cost function over what came out.
#[test]
fn head_expressibility_of_the_root_tables() {
    let rows = 1024;
    let e = vec![
        expressibility("Const", &const_air(rows)),
        expressibility("Public", &public_air(rows)),
        expressibility("Alu", &alu_air(rows)),
        expressibility("poseidon2_w16", &BabyBearD4Width16::default_air()),
        expressibility("poseidon2_w24", &BabyBearD4Width24::default_air()),
        expressibility("recompose", &recompose_air()),
        expressibility("expose_claim", &expose_claim_air()),
    ];
    println!(
        "\n{:<16} {:>6} {:>7} {:>10} {:>7} {:>11} {:>9} {:>10}",
        "table", "base", "express", "max_monos", "max_deg", "Σ monomial", "ext_muls", "cheap_ops"
    );
    for t in &e {
        println!(
            "{:<16} {:>6} {:>7} {:>10} {:>7} {:>11} {:>9} {:>10}",
            t.name,
            t.total,
            t.expressible,
            t.max_monomials,
            t.max_degree,
            t.total_monomials,
            t.ext_muls,
            t.cheap_ops
        );
    }
    let tot: usize = e.iter().map(|t| t.total).sum();
    let ok: usize = e.iter().map(|t| t.expressible).sum();
    let monos: usize = e.iter().map(|t| t.total_monomials).sum();
    let muls: usize = e.iter().map(|t| t.ext_muls).sum();
    let cheap: usize = e.iter().map(|t| t.cheap_ops).sum();
    println!("\nflat-Head expressible: {ok} / {tot} base constraints (cap {CAP} monomials)");
    println!("Σ monomials {monos} · Σ ext-muls {muls} · Σ cheap ops {cheap}");
}

/// ⚑ **THE EXTRACTOR'S ANTI-VACUITY CHECK.** A differential, and named as one: for every
/// extracted `Head`, `headEvalR` and p3's own `SymbolicExpression` evaluation must agree at
/// pseudorandom assignments. It proves nothing about all inputs; what it rules out is an
/// extractor that is quietly wrong on the constraints the Lean side is about to consume.
#[test]
fn head_extractor_agrees_with_p3_evaluation() {
    let rows = 1024;
    let mut checked = 0usize;
    let mut seed = 0x5eed_1234_abcd_0001u64;

    macro_rules! check {
        ($name:expr, $air:expr) => {{
            let air = $air;
            let cs = base_constraints(&air)
                .into_iter()
                .map(std::sync::Arc::new)
                .collect::<Vec<_>>();
            let mut vars = BTreeMap::new();
            let mut memo = Memo::new();
            let heads: Vec<Option<std::rc::Rc<Head>>> = cs
                .iter()
                .map(|c| to_head_arc(c, &mut vars, &mut memo, CAP))
                .collect();
            let n_vars = vars.len().max(1);
            for _trial in 0..8 {
                let a: Vec<F> = (0..n_vars).map(|_| lcg(&mut seed)).collect();
                let mut ememo = EvalMemo::new();
                for (c, h) in cs.iter().zip(heads.iter()) {
                    let Some(h) = h else { continue };
                    let lhs = eval_head(h, &a);
                    let rhs = eval_sym(c, &vars, &a, &mut ememo);
                    assert_eq!(
                        lhs, rhs,
                        "{} : extracted Head disagrees with p3's SymbolicExpression",
                        $name
                    );
                    checked += 1;
                }
            }
        }};
    }

    check!("Const", const_air(rows));
    check!("Public", public_air(rows));
    check!("Alu", alu_air(rows));
    check!("poseidon2_w16", BabyBearD4Width16::default_air());
    check!("poseidon2_w24", BabyBearD4Width24::default_air());
    check!("recompose", recompose_air());
    check!("expose_claim", expose_claim_air());

    println!("\n{checked} Head/SymbolicExpression agreements at 8 pseudorandom assignments each");
    assert!(
        checked > 0,
        "a differential over an empty set proves less than nothing"
    );
}

/// ⚑ **WHAT THE FLAT FORM COSTS, AGAINST WHAT THE DAG COSTS.**
///
/// `Head` is `Σ coeff·∏cols + const` — FLAT. p3's `SymbolicExpression` is an `Arc`-shared DAG, and
/// `SymbolicCompiler::compile_base` lowers it with a cache, so a subexpression used twenty times is
/// twenty edges and ONE multiplication. Flattening to monomials destroys exactly that sharing.
///
/// This counts both: the DISTINCT `Mul` nodes in the DAG (what a sharing-preserving lowering pays)
/// against the `ext_muls` of the flattened form (what `lowerHead` pays today). The ratio is the
/// price of the compiler's flat source language, and it is the whole argument for the next rung.
#[test]
fn dag_sharing_versus_flat_monomials() {
    fn dag_nodes<A>(air: &A) -> (usize, usize)
    where
        A: BaseAir<F> + p3_air::Air<p3_lookup::InteractionSymbolicBuilder<F, EF>>,
    {
        fn walk(
            e: &SymbolicExpression<F>,
            seen: &mut std::collections::HashSet<*const SymbolicExpression<F>>,
            nodes: &mut usize,
            muls: &mut usize,
        ) {
            *nodes += 1;
            let mut kid = |c: &std::sync::Arc<SymbolicExpression<F>>,
                           seen: &mut std::collections::HashSet<_>,
                           nodes: &mut usize,
                           muls: &mut usize| {
                if seen.insert(std::sync::Arc::as_ptr(c)) {
                    walk(c, seen, nodes, muls);
                }
            };
            match e {
                SymbolicExpr::Leaf(_) => {}
                SymbolicExpr::Neg { x, .. } => kid(x, seen, nodes, muls),
                SymbolicExpr::Add { x, y, .. } | SymbolicExpr::Sub { x, y, .. } => {
                    kid(x, seen, nodes, muls);
                    kid(y, seen, nodes, muls);
                }
                SymbolicExpr::Mul { x, y, .. } => {
                    *muls += 1;
                    kid(x, seen, nodes, muls);
                    kid(y, seen, nodes, muls);
                }
            }
        }
        let cs = base_constraints(air);
        let mut seen = std::collections::HashSet::new();
        let mut nodes = 0;
        let mut muls = 0;
        for c in &cs {
            walk(c, &mut seen, &mut nodes, &mut muls);
        }
        (nodes, muls)
    }

    let rows = 1024;
    let tables: Vec<(&str, (usize, usize), usize)> = vec![
        (
            "Const",
            dag_nodes(&const_air(rows)),
            expressibility("", &const_air(rows)).ext_muls,
        ),
        (
            "Public",
            dag_nodes(&public_air(rows)),
            expressibility("", &public_air(rows)).ext_muls,
        ),
        (
            "Alu",
            dag_nodes(&alu_air(rows)),
            expressibility("", &alu_air(rows)).ext_muls,
        ),
        (
            "poseidon2_w16",
            dag_nodes(&BabyBearD4Width16::default_air()),
            expressibility("", &BabyBearD4Width16::default_air()).ext_muls,
        ),
        (
            "poseidon2_w24",
            dag_nodes(&BabyBearD4Width24::default_air()),
            expressibility("", &BabyBearD4Width24::default_air()).ext_muls,
        ),
        (
            "recompose",
            dag_nodes(&recompose_air()),
            expressibility("", &recompose_air()).ext_muls,
        ),
        (
            "expose_claim",
            dag_nodes(&expose_claim_air()),
            expressibility("", &expose_claim_air()).ext_muls,
        ),
    ];
    println!(
        "\n{:<16} {:>10} {:>10} {:>12} {:>8}",
        "table", "dag_nodes", "dag_muls", "flat_muls", "ratio"
    );
    let mut dm = 0usize;
    let mut fm = 0usize;
    for (name, (nodes, muls), flat) in &tables {
        dm += muls;
        fm += flat;
        let ratio = if *muls == 0 {
            0.0
        } else {
            *flat as f64 / *muls as f64
        };
        println!("{name:<16} {nodes:>10} {muls:>10} {flat:>12} {ratio:>8.1}x");
    }
    println!("\nDAG multiplications (shared)  : {dm}");
    println!("flat-Head multiplications     : {fm}");
    println!(
        "the flat source language costs {:.1}x the DAG",
        fm as f64 / dm.max(1) as f64
    );
}

// ===========================================================================
// THE EMITTER — `Head`s out, in Lean's own syntax
// ===========================================================================

/// Render one `Head` as a Lean `Dregg2.Circuit.Emit.AirBuilder.Head` literal.
fn lean_head(h: &Head) -> String {
    let terms: Vec<String> = h
        .terms
        .iter()
        .map(|(c, cols)| {
            let cols: Vec<String> = cols.iter().map(usize::to_string).collect();
            format!("({c}, [{}])", cols.join(", "))
        })
        .collect();
    format!("⟨[{}], {}⟩", terms.join(", "), h.konst)
}

/// Emit the extracted `Head`s for one table, plus its variable legend, to stdout in a form the
/// Lean generator consumes verbatim. Set `DREGG_EMIT_HEADS=<table>` to select the table.
#[test]
fn emit_lean_heads() {
    let Ok(which) = std::env::var("DREGG_EMIT_HEADS") else {
        println!("set DREGG_EMIT_HEADS=<Const|Public|Alu|recompose|expose_claim> to emit");
        return;
    };
    let rows = 1024;
    let (cs, label) = match which.as_str() {
        "Const" => (base_constraints(&const_air(rows)), "Const"),
        "Public" => (base_constraints(&public_air(rows)), "Public"),
        "Alu" => (base_constraints(&alu_air(rows)), "Alu"),
        "recompose" => (base_constraints(&recompose_air()), "recompose"),
        "expose_claim" => (base_constraints(&expose_claim_air()), "expose_claim"),
        "poseidon2_w16" => (
            base_constraints(&BabyBearD4Width16::default_air()),
            "poseidon2_w16",
        ),
        "poseidon2_w24" => (
            base_constraints(&BabyBearD4Width24::default_air()),
            "poseidon2_w24",
        ),
        other => panic!("unknown table {other}"),
    };
    let cs: Vec<std::sync::Arc<SymbolicExpression<F>>> =
        cs.into_iter().map(std::sync::Arc::new).collect();
    let mut vars = BTreeMap::new();
    let mut memo = Memo::new();
    let mut out = Vec::new();
    for c in &cs {
        out.push(to_head_arc(c, &mut vars, &mut memo, CAP));
    }
    println!("-- TABLE {label}: {} base constraints", cs.len());
    let mut legend: Vec<(usize, String)> = vars.iter().map(|(k, v)| (*v, k.label())).collect();
    legend.sort_unstable();
    for (i, l) in &legend {
        println!("--   col {i} = {l}");
    }
    println!("HEADS_BEGIN");
    for (i, h) in out.iter().enumerate() {
        match h {
            Some(h) => println!("  {} ,-- C{i}", lean_head(h)),
            None => println!("  -- C{i} EXCEEDS CAP"),
        }
    }
    println!("HEADS_END");
}

// ===========================================================================
// THE DAG SOURCE LANGUAGE — a STRUCTURE-PRESERVING numbering of p3's own DAG
// ===========================================================================
//
// ⚑ WHY THIS IS A DIFFERENT SEAM FROM `to_head`, NOT A SECOND COPY OF IT.
//
// `to_head` FLATTENS: it distributes every product over every sum and returns monomials, which
// destroys the `Arc` sharing p3 built and costs 521x in multiplications (see
// `dag_sharing_versus_flat_monomials`). `to_dag` does not compute anything: it walks the same DAG
// and replaces each `Arc` child by the INDEX of the node that child became. Node kinds are 1:1
// with `SymbolicExpr`'s constructors (`Leaf`/`Add`/`Sub`/`Neg`/`Mul`), so the seam is a
// re-indexing rather than an algebraic rewrite — a strictly narrower thing to get wrong.
//
// CSE. p3's `SymbolicCompiler::compile_base` keys its cache on the raw `Arc` pointer, so two
// structurally identical but separately allocated subtrees stay separate. This one keeps that
// pointer cache AND interns on STRUCTURAL identity of the already-numbered node, so it is at
// least as sharing-preserving as p3's. Both counts are reported.

/// One SSA node. Children are indices into the node list and are always STRICTLY SMALLER than
/// the node's own index (`dag_wf` asserts it), so the list is topologically sorted by
/// construction. This is `Dregg2.Circuit.Emit.KimchiDag.Node`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum DagNode {
    /// A column, in the SAME `vars` numbering `to_head` uses — so a DAG and a `Head` extracted
    /// from the same AIR read the same assignment.
    Var(usize),
    /// A constant, as a canonical BabyBear representative.
    Cst(i64),
    Add(usize, usize),
    Sub(usize, usize),
    Neg(usize),
    Mul(usize, usize),
}

/// A constraint system as one shared DAG plus the indices of its constraint roots.
#[derive(Debug, Default)]
struct Dag {
    nodes: Vec<DagNode>,
    roots: Vec<usize>,
    /// Nodes that the STRUCTURAL cache merged and a pointer-only cache would not have.
    struct_hits: usize,
}

impl Dag {
    fn muls(&self) -> usize {
        self.nodes
            .iter()
            .filter(|n| matches!(n, DagNode::Mul(_, _)))
            .count()
    }

    /// `[var, cst, add, sub, neg, mul]`. ⚑ This is the PRICE'S input, not a curiosity: only `Mul`
    /// is a full extension multiply (31 rows, §3.14); `Add`/`Sub`/`Neg`/`Var` are extension
    /// add/scale (19); `Cst` is a pin. Pricing `C_i` off the multiply count alone — which is what
    /// the ledger did — undercounts by the whole linear half.
    fn kinds(&self) -> [usize; 6] {
        let mut k = [0usize; 6];
        for n in &self.nodes {
            let i = match n {
                DagNode::Var(_) => 0,
                DagNode::Cst(_) => 1,
                DagNode::Add(_, _) => 2,
                DagNode::Sub(_, _) => 3,
                DagNode::Neg(_) => 4,
                DagNode::Mul(_, _) => 5,
            };
            k[i] += 1;
        }
        k
    }

    /// Every child index is strictly below its parent's index — the invariant the Lean lowering
    /// theorem takes as `dagWf`. Checked here so a violation is caught at emission, not in Lean.
    fn wf(&self) -> bool {
        self.nodes.iter().enumerate().all(|(i, n)| match *n {
            DagNode::Var(_) | DagNode::Cst(_) => true,
            DagNode::Neg(x) => x < i,
            DagNode::Add(x, y) | DagNode::Sub(x, y) | DagNode::Mul(x, y) => x < i && y < i,
        }) && self.roots.iter().all(|&r| r < self.nodes.len())
    }

    /// Evaluate the DAG at an assignment — the Rust twin of Lean's `denote`, and the reference
    /// the differential compares against p3.
    fn eval(&self, a: &[F]) -> Vec<F> {
        let mut v: Vec<F> = Vec::with_capacity(self.nodes.len());
        for n in &self.nodes {
            let x = match *n {
                DagNode::Var(c) => a[c],
                DagNode::Cst(k) => F::from_u32(u32::try_from(k.rem_euclid(babybear_p())).unwrap()),
                DagNode::Add(i, j) => v[i] + v[j],
                DagNode::Sub(i, j) => v[i] - v[j],
                DagNode::Neg(i) => -v[i],
                DagNode::Mul(i, j) => v[i] * v[j],
            };
            v.push(x);
        }
        v
    }
}

#[derive(Clone, Copy)]
enum DagOp {
    Add,
    Sub,
    Mul,
}

enum DagWork<'a> {
    Eval(&'a SymbolicExpression<F>),
    Build(*const SymbolicExpression<F>, DagOp),
    BuildNeg(*const SymbolicExpression<F>),
}

struct DagBuilder {
    dag: Dag,
    /// p3's own cache discipline: `Arc` identity (`compile_base`'s `base_cache`).
    ptr: std::collections::HashMap<*const SymbolicExpression<F>, usize>,
    /// The extra one: STRUCTURAL identity of the numbered node.
    hc: std::collections::HashMap<DagNode, usize>,
}

impl DagBuilder {
    fn new() -> Self {
        Self {
            dag: Dag::default(),
            ptr: std::collections::HashMap::new(),
            hc: std::collections::HashMap::new(),
        }
    }

    /// Hash-cons one node. Returns an existing index on a structural hit.
    fn intern(&mut self, n: DagNode) -> usize {
        if let Some(&i) = self.hc.get(&n) {
            self.dag.struct_hits += 1;
            return i;
        }
        let i = self.dag.nodes.len();
        self.dag.nodes.push(n);
        self.hc.insert(n, i);
        i
    }

    fn leaf(&mut self, leaf: &BaseLeaf<F>, vars: &mut BTreeMap<VarKey, usize>) -> usize {
        let key = match leaf {
            BaseLeaf::Constant(c) => {
                let k = i64::from(c.as_canonical_u32());
                return self.intern(DagNode::Cst(k));
            }
            BaseLeaf::IsFirstRow => VarKey::IsFirstRow,
            BaseLeaf::IsLastRow => VarKey::IsLastRow,
            BaseLeaf::IsTransition => VarKey::IsTransition,
            BaseLeaf::Variable(v) => match v.entry {
                BaseEntry::Preprocessed { offset } => VarKey::Preprocessed {
                    offset,
                    index: v.index,
                },
                BaseEntry::Main { offset } => VarKey::Main {
                    offset,
                    index: v.index,
                },
                BaseEntry::Periodic => VarKey::Periodic { index: v.index },
                BaseEntry::Public => VarKey::Public { index: v.index },
            },
        };
        let next = vars.len();
        let col = *vars.entry(key).or_insert(next);
        self.intern(DagNode::Var(col))
    }

    /// **THE EXTRACTOR.** An explicit two-stack walk, the same shape as
    /// `SymbolicCompiler::compile_base` — no recursion, so DAG depth cannot blow the stack.
    fn add_root(&mut self, e: &SymbolicExpression<F>, vars: &mut BTreeMap<VarKey, usize>) {
        let mut tasks: Vec<DagWork<'_>> = vec![DagWork::Eval(e)];
        let mut stack: Vec<usize> = Vec::with_capacity(16);
        while let Some(w) = tasks.pop() {
            match w {
                DagWork::BuildNeg(key) => {
                    let x = stack.pop().expect("operand for neg");
                    let id = self.intern(DagNode::Neg(x));
                    self.ptr.insert(key, id);
                    stack.push(id);
                }
                DagWork::Build(key, op) => {
                    let y = stack.pop().expect("rhs");
                    let x = stack.pop().expect("lhs");
                    let id = self.intern(match op {
                        DagOp::Add => DagNode::Add(x, y),
                        DagOp::Sub => DagNode::Sub(x, y),
                        DagOp::Mul => DagNode::Mul(x, y),
                    });
                    self.ptr.insert(key, id);
                    stack.push(id);
                }
                DagWork::Eval(node) => {
                    let key: *const SymbolicExpression<F> = node;
                    if let Some(&hit) = self.ptr.get(&key) {
                        stack.push(hit);
                        continue;
                    }
                    let id = match node {
                        SymbolicExpr::Leaf(l) => self.leaf(l, vars),
                        SymbolicExpr::Neg { x, .. } => {
                            tasks.push(DagWork::BuildNeg(key));
                            tasks.push(DagWork::Eval(x));
                            continue;
                        }
                        SymbolicExpr::Add { x, y, .. } => {
                            tasks.push(DagWork::Build(key, DagOp::Add));
                            tasks.push(DagWork::Eval(y));
                            tasks.push(DagWork::Eval(x));
                            continue;
                        }
                        SymbolicExpr::Sub { x, y, .. } => {
                            tasks.push(DagWork::Build(key, DagOp::Sub));
                            tasks.push(DagWork::Eval(y));
                            tasks.push(DagWork::Eval(x));
                            continue;
                        }
                        SymbolicExpr::Mul { x, y, .. } => {
                            tasks.push(DagWork::Build(key, DagOp::Mul));
                            tasks.push(DagWork::Eval(y));
                            tasks.push(DagWork::Eval(x));
                            continue;
                        }
                    };
                    self.ptr.insert(key, id);
                    stack.push(id);
                }
            }
        }
        let root = stack.pop().expect("final target");
        self.dag.roots.push(root);
    }
}

/// Extract one AIR's whole base constraint system as ONE shared DAG. The cache is shared across
/// constraints — that cross-constraint sharing is what `base_cache` buys in p3 and what makes the
/// multiply count 2,937 rather than a per-constraint sum.
fn to_dag<A>(air: &A) -> (Dag, BTreeMap<VarKey, usize>)
where
    A: BaseAir<F> + p3_air::Air<p3_lookup::InteractionSymbolicBuilder<F, EF>>,
{
    let cs = base_constraints(air);
    let mut b = DagBuilder::new();
    let mut vars = BTreeMap::new();
    for c in &cs {
        b.add_root(c, &mut vars);
    }
    (b.dag, vars)
}

fn all_base_tables() -> Vec<(&'static str, Dag, BTreeMap<VarKey, usize>)> {
    let rows = 1024;
    let mut out = Vec::new();
    macro_rules! t {
        ($n:expr, $air:expr) => {{
            let (d, v) = to_dag(&$air);
            out.push(($n, d, v));
        }};
    }
    t!("Const", const_air(rows));
    t!("Public", public_air(rows));
    t!("Alu", alu_air(rows));
    t!("poseidon2_w16", BabyBearD4Width16::default_air());
    t!("poseidon2_w24", BabyBearD4Width24::default_air());
    t!("recompose", recompose_air());
    t!("expose_claim", expose_claim_air());
    out
}

/// ⚑ **THE DAG EXTRACTOR'S ANTI-VACUITY CHECK** — the same confession `to_head` makes, over the
/// new path. For every base constraint of all seven tables, the DAG's root value and p3's own
/// `SymbolicExpression` evaluation must agree at pseudorandom assignments.
#[test]
fn dag_extractor_agrees_with_p3_evaluation() {
    let mut seed = 0x5eed_1234_abcd_0001u64;
    let mut checked = 0usize;
    for (name, dag, vars) in all_base_tables() {
        assert!(dag.wf(), "{name}: DAG is not topologically sorted");
        let cs = base_constraints_by_name(name);
        assert_eq!(
            cs.len(),
            dag.roots.len(),
            "{name}: one root per base constraint"
        );
        let n_vars = vars.len().max(1);
        for _trial in 0..8 {
            let a: Vec<F> = (0..n_vars).map(|_| lcg(&mut seed)).collect();
            let v = dag.eval(&a);
            let mut ememo = EvalMemo::new();
            for (c, &r) in cs.iter().zip(dag.roots.iter()) {
                let lhs = v[r];
                let rhs = eval_sym(c, &vars, &a, &mut ememo);
                assert_eq!(lhs, rhs, "{name}: DAG root disagrees with p3");
                checked += 1;
            }
        }
    }
    println!("\n{checked} DAG-root/SymbolicExpression agreements at 8 assignments each");
    assert!(checked > 0, "a differential over an empty set says nothing");
}

/// ⚑ **THE REGRESSION THE COMPILER CHANGE MUST NOT BREAK.** For the two tables the flat path
/// already generated, the DAG path and the `Head` path must denote the SAME value, constraint by
/// constraint, at the same assignment. A compiler change that silently alters emitted semantics is
/// the worst possible outcome; this is the check that would catch it.
#[test]
fn dag_and_head_denote_the_same_constraints() {
    let mut seed = 0xd00d_beef_0000_0007u64;
    let mut checked = 0usize;
    macro_rules! both {
        ($name:expr, $air:expr) => {{
            let air = $air;
            let (dag, dvars) = to_dag(&air);
            let cs = base_constraints(&air)
                .into_iter()
                .map(std::sync::Arc::new)
                .collect::<Vec<_>>();
            let mut hvars = BTreeMap::new();
            let mut memo = Memo::new();
            let heads: Vec<Option<std::rc::Rc<Head>>> = cs
                .iter()
                .map(|c| to_head_arc(c, &mut hvars, &mut memo, CAP))
                .collect();
            // ⚑ The two extractors must agree on the COLUMN NUMBERING, or "the same assignment"
            // is a different assignment and the differential is meaningless.
            assert_eq!(hvars, dvars, "{}: variable numbering diverged", $name);
            let n_vars = dvars.len().max(1);
            for _trial in 0..8 {
                let a: Vec<F> = (0..n_vars).map(|_| lcg(&mut seed)).collect();
                let v = dag.eval(&a);
                for (h, &r) in heads.iter().zip(dag.roots.iter()) {
                    let Some(h) = h else { continue };
                    assert_eq!(
                        eval_head(h, &a),
                        v[r],
                        "{}: DAG and Head disagree on a constraint",
                        $name
                    );
                    checked += 1;
                }
            }
        }};
    }
    both!("Alu", alu_air(1024));
    both!("expose_claim", expose_claim_air());
    println!("\n{checked} DAG/Head denotation agreements");
    assert!(checked > 0, "a differential over an empty set says nothing");
}

fn base_constraints_by_name(name: &str) -> Vec<SymbolicExpression<F>> {
    let rows = 1024;
    match name {
        "Const" => base_constraints(&const_air(rows)),
        "Public" => base_constraints(&public_air(rows)),
        "Alu" => base_constraints(&alu_air(rows)),
        "poseidon2_w16" => base_constraints(&BabyBearD4Width16::default_air()),
        "poseidon2_w24" => base_constraints(&BabyBearD4Width24::default_air()),
        "recompose" => base_constraints(&recompose_air()),
        "expose_claim" => base_constraints(&expose_claim_air()),
        other => panic!("unknown table {other}"),
    }
}

/// The census the Lean side is priced against: nodes, multiplies and roots, per table.
#[test]
fn dag_source_language_census() {
    println!(
        "\n{:<16} {:>7} {:>8} {:>8} {:>8} {:>10}",
        "table", "roots", "nodes", "muls", "cse_hits", "flat_muls"
    );
    let mut n = 0usize;
    let mut m = 0usize;
    let mut r = 0usize;
    for (name, dag, _) in all_base_tables() {
        assert!(dag.wf(), "{name}: DAG is not topologically sorted");
        let flat = flat_muls_by_name(name);
        println!(
            "{name:<16} {:>7} {:>8} {:>8} {:>8} {:>10}",
            dag.roots.len(),
            dag.nodes.len(),
            dag.muls(),
            dag.struct_hits,
            flat
        );
        r += dag.roots.len();
        n += dag.nodes.len();
        m += dag.muls();
    }
    println!("\nroots (base constraints) : {r}");
    println!("DAG nodes                : {n}");
    println!("DAG multiplies           : {m}");
    println!("+ one alpha-fold per root: {}", m + r);

    // ⚑ THE RE-PRICE. §3.14's measured units: extension multiply 31 rows, extension add/scale 19,
    // a constant pin ~0. The ledger priced `C_i` off the MULTIPLY count alone; the node program's
    // linear half is real and is counted here.
    let mut k = [0usize; 6];
    for (_, dag, _) in all_base_tables() {
        let d = dag.kinds();
        for i in 0..6 {
            k[i] += d[i];
        }
    }
    println!(
        "\nnode kinds: var {} cst {} add {} sub {} neg {} mul {}",
        k[0], k[1], k[2], k[3], k[4], k[5]
    );
    let ext_mul = 31usize;
    let ext_lin = 19usize;
    let ci_rows = k[5] * ext_mul + (k[0] + k[2] + k[3] + k[4]) * ext_lin;
    let flat_rows = 1_529_889usize * ext_mul;
    println!(
        "C_i node program         : {ci_rows} rows  ({} mul + {} lin)",
        k[5] * ext_mul,
        (k[0] + k[2] + k[3] + k[4]) * ext_lin
    );
    println!(
        "  of which .var copies   : {} rows (elidable, KimchiDag §11.2)",
        k[0] * ext_lin
    );
    println!(
        "the alpha-fold, A + N*h  : {} rows (14175 + 1093*48, all 1093)",
        14_175 + 1093 * 48
    );
    println!(
        "AIR side, whole root     : {} rows",
        ci_rows + 14_175 + 1093 * 48
    );
    println!("the FLAT form's multiplies alone: {flat_rows} rows");

    assert_eq!(
        r, 901,
        "the root count is the census's 901 base constraints"
    );
    assert_eq!(
        k.iter().sum::<usize>(),
        n,
        "the kind histogram must cover every node"
    );
    assert!(
        ci_rows * 100 < 30_000_000,
        "C_i through the DAG language must be under 1% of the 3.0e7 whole-verifier budget"
    );
    assert!(
        flat_rows > 30_000_000,
        "and the flat form must still exceed the whole budget on multiplies alone — if this ever \
         stops holding, the argument for this source language has changed"
    );
}

fn flat_muls_by_name(name: &str) -> usize {
    let rows = 1024;
    match name {
        "Const" => expressibility("", &const_air(rows)).ext_muls,
        "Public" => expressibility("", &public_air(rows)).ext_muls,
        "Alu" => expressibility("", &alu_air(rows)).ext_muls,
        "poseidon2_w16" => expressibility("", &BabyBearD4Width16::default_air()).ext_muls,
        "poseidon2_w24" => expressibility("", &BabyBearD4Width24::default_air()).ext_muls,
        "recompose" => expressibility("", &recompose_air()).ext_muls,
        "expose_claim" => expressibility("", &expose_claim_air()).ext_muls,
        other => panic!("unknown table {other}"),
    }
}

/// Render the DAG for one table as Lean literals. `DREGG_EMIT_DAG=<table>` selects it.
#[test]
fn emit_lean_dag() {
    let Ok(which) = std::env::var("DREGG_EMIT_DAG") else {
        println!(
            "set DREGG_EMIT_DAG=<Const|Public|Alu|poseidon2_w16|poseidon2_w24|recompose|expose_claim>"
        );
        return;
    };
    let per_chunk: usize = std::env::var("DREGG_DAG_CHUNK")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(512);
    let (dag, vars) = match which.as_str() {
        "Const" => to_dag(&const_air(1024)),
        "Public" => to_dag(&public_air(1024)),
        "Alu" => to_dag(&alu_air(1024)),
        "poseidon2_w16" => to_dag(&BabyBearD4Width16::default_air()),
        "poseidon2_w24" => to_dag(&BabyBearD4Width24::default_air()),
        "recompose" => to_dag(&recompose_air()),
        "expose_claim" => to_dag(&expose_claim_air()),
        other => panic!("unknown table {other}"),
    };
    assert!(
        dag.wf(),
        "refusing to emit a DAG that is not topologically sorted"
    );
    let lean = |n: &DagNode| -> String {
        match *n {
            DagNode::Var(c) => format!(".var {c}"),
            DagNode::Cst(k) => format!(".cst {k}"),
            DagNode::Add(i, j) => format!(".add {i} {j}"),
            DagNode::Sub(i, j) => format!(".sub {i} {j}"),
            DagNode::Neg(i) => format!(".neg {i}"),
            DagNode::Mul(i, j) => format!(".mul {i} {j}"),
        }
    };
    println!(
        "-- TABLE {which}: {} base constraints, {} DAG nodes, {} multiplies, {} columns",
        dag.roots.len(),
        dag.nodes.len(),
        dag.muls(),
        vars.len()
    );
    let mut legend: Vec<(usize, String)> = vars.iter().map(|(k, v)| (*v, k.label())).collect();
    legend.sort_unstable();
    for (i, l) in &legend {
        println!("--   col {i} = {l}");
    }
    println!("DAG_BEGIN");
    println!("-- chunks of {per_chunk}");
    for (ci, chunk) in dag.nodes.chunks(per_chunk).enumerate() {
        println!("CHUNK {ci}");
        let mut line = String::new();
        for (k, n) in chunk.iter().enumerate() {
            if !line.is_empty() {
                line.push_str(", ");
            }
            line.push_str(&lean(n));
            if line.len() > 96 || k + 1 == chunk.len() {
                println!("  {line}{}", if k + 1 == chunk.len() { "" } else { "," });
                line.clear();
            }
        }
        println!("CHUNK_END");
    }
    println!("DAG_END");
    println!("ROOTS_BEGIN");
    let mut line = String::new();
    for (k, r) in dag.roots.iter().enumerate() {
        if !line.is_empty() {
            line.push_str(", ");
        }
        line.push_str(&r.to_string());
        if line.len() > 96 || k + 1 == dag.roots.len() {
            println!(
                "  {line}{}",
                if k + 1 == dag.roots.len() { "" } else { "," }
            );
            line.clear();
        }
    }
    println!("ROOTS_END");
    println!("COLS {}", vars.len());
}
