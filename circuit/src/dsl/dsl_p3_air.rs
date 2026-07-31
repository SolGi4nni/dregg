//! Real Plonky3 `Air<AB>` for the DSL circuit interpreter — the migration off
//! the bespoke `crate::stark` prover/verifier for the **live Lean-emitted
//! circuit TCB**.
//!
//! ## Why this exists (the TCB-shrinking point)
//!
//! The live circuit IR is built and proved sound in Lean
//! (`metatheory/Dregg2/Circuit/*`, emitted via `Dregg2.Exec.CircuitEmit` as a
//! column-indexed `ConstraintExpr` AST). That AST is decoded by the Rust
//! `circuit/src/dsl/circuit.rs::DslCircuit`, which — until now — proved and
//! verified through the **hand-rolled** `crate::stark` STARK (`stark::prove` /
//! `stark::verify`). That bespoke prover has a hand-rolled FRI whose final
//! low-degree test is effectively absent and whose trace columns are never
//! low-degree-tested (see the soundness review in `crate::stark`). Running the
//! verified circuit through it puts an unaudited verifier in the live TCB.
//!
//! This module replaces that path with the **audited Plonky3 verifier**:
//! [`DslP3Air`] emits the *same* algebraic constraints symbolically against a
//! `p3-air::AirBuilder`, and [`prove_dsl_p3`] / [`verify_dsl_p3`] route them
//! through `p3-batch-stark` (`prove_batch` / `verify_batch`) using the same
//! production config (`create_config`) the other migrated AIRs use
//! (`lean_descriptor_air`, `lean_lookup_air`, `joint_turn_aggregation`).
//!
//! ## Faithfulness to `DslCircuit`
//!
//! Every algebraic `ConstraintExpr` arm here is the symbolic mirror of the
//! concrete arm in `ConstraintExpr::evaluate_with_tables`:
//!
//! | `ConstraintExpr`        | concrete (`evaluate`)                     | symbolic (here)                          |
//! |-------------------------|-------------------------------------------|------------------------------------------|
//! | `Equality{a,b}`         | `local[a] - local[b]`                     | `assert_zero(a - b)`                     |
//! | `Multiplication{a,b,o}` | `local[a]*local[b] - local[o]`            | `assert_zero(a*b - o)`                   |
//! | `Binary{c}`             | `c*(c-1)`                                 | `assert_zero(c*(c-1))`                   |
//! | `PiBinding{c,i}`        | `local[c] - pi[i]`                        | `assert_zero(c - public_values[i])`      |
//! | `Transition{n,l}`       | `next[n] - local[l]`                      | `when_transition().assert_zero(n' - l)`  |
//! | `Polynomial{terms}`     | `Σ coeff·Π local[ci]`                     | `assert_zero(Σ coeff·Π ci)`              |
//! | `Gated{s,inner}`        | `local[s]·inner`                          | `assert_zero(s·inner)`                   |
//!
//! ⚠ That `Gated` row holds ONLY for an algebraic `inner`. A hash form wrapped in
//! `Gated`/`InvertedGated`/`Squared` has NO faithful row here: `is_hash` matches
//! only top-level forms, so a wrapped hash was allocated no Poseidon2 aux block and
//! folded through `eval_expr` to `AB::Expr::ZERO`, emitting `assert_zero(s · 0)` —
//! satisfied by EVERY assignment, selector on or off. Not gated off: **erased.**
//! Measured 2026-07-30 on the deployed shielded-spend descriptor, whose nullifier
//! binding C4 was exactly that shape. `try_from_dsl` now REFUSES such a descriptor
//! ([`DslP3Error::ErasedConstraint`]) and a standing count of allocated aux blocks
//! against contained hash forms backs the refusal up form-agnostically.
//! | `InvertedGated{s,inner}`| `(1-local[s])·inner`                      | `assert_zero((1-s)·inner)`               |
//! | `Squared{inner}`        | `inner²`                                  | `assert_zero(inner²)`                    |
//! | `ConditionalNonzero`    | `s·(v·inv - 1)`                           | `assert_zero(s·(v·inv - 1))`             |
//! | `AtLeastOne{flags}`     | `Π(1-fi)`                                 | `assert_zero(Π(1-fi))`                   |
//!
//! Boundary `PiBinding`/`Fixed` map to `when_first_row()` / `when_last_row()`
//! (and absolute-row gating) `assert_zero` exactly as `DslCircuit`'s
//! `boundary_constraints` resolves them.
//!
//! ## What is NOT translated (and why this is sound, not a downgrade)
//!
//! `Hash`, `Hash2to1`, `Hash4to1`, `MerkleHash`, and `Lookup` compute a
//! Poseidon2 permutation / table-membership *concretely* on the trace cells.
//! These are not polynomial constraints (the DSL marks their degree as 1 and the
//! bespoke verifier only "checks" them by re-running the hash on opened cells at
//! trace rows — they do not constrain the low-degree extension at all). They
//! CANNOT be expressed against a symbolic `AirBuilder` without a real Poseidon2
//! round arithmetization (the p3 path for those is the dedicated
//! `lean_descriptor_air` / `lean_lookup_air` AIRs, which DO arithmetize them).
//!
//! Rather than silently drop them (which would forge soundness), [`prove_dsl_p3`]
//! returns [`DslP3Error::NonAlgebraicConstraint`] if the descriptor contains any
//! such form. A caller wanting to prove a hash/lookup circuit through real p3
//! must route it through the arithmetized AIRs. This module covers the
//! algebraic core (the Transfer / balance / selector / boundary spine — the
//! anti-ghost commit tooth) on the audited verifier.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_batch_stark::{BatchProof, ProverData, StarkInstance, prove_batch, verify_batch};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;

use p3_field::PrimeField32;

use crate::dsl::circuit::{BoundaryDef, BoundaryRow, ConstraintExpr, DslCircuit};
use crate::field::BabyBear;
use crate::plonky3_prover::{
    DreggStarkConfig, POSEIDON2_PERM_AUX_COLS, POSEIDON2_WIDTH, create_config,
    poseidon2_permute_aux_witness, poseidon2_permute_expr, poseidon2_permute_expr_lanes, to_p3,
};

/// The DSL-circuit p3 proof: a `p3-batch-stark` batch proof over the production
/// `DreggStarkConfig` (the audited Plonky3 verifier).
pub type DslP3Proof = BatchProof<DreggStarkConfig>;

/// A descriptor-driven AIR that emits the DSL circuit's algebraic constraints
/// symbolically against `p3-air`, so the real Plonky3 prover/verifier consume
/// it directly. Clone of the descriptor (it is `Clone` and small).
#[derive(Clone, Debug)]
pub struct DslP3Air {
    descriptor: crate::dsl::circuit::CircuitDescriptor,
    /// Base trace width (descriptor columns) without Poseidon2 aux blocks.
    base_width: usize,
    /// FULL trace width = base_width + num_hashes * POSEIDON2_PERM_AUX_COLS +
    /// interior-row selector aux block.
    full_width: usize,
    /// Column where the interior-row selector aux block begins (counter + per
    /// interior-boundary IsZero witness). == base_width + hash aux blocks.
    interior_aux_base: usize,
}

impl DslP3Air {
    /// Build a p3 AIR from a `DslCircuit`. Fails ONLY on `MerkleHash` (use the Lean-emitted IR2
    /// descriptor for position-indexed Merkle hashing) and `Lookup` (route through the LogUp bus /
    /// `lean_lookup_air`). Everything else is supported: the algebraic forms AND the Poseidon2 hash
    /// forms — `Hash` (sponge), `Hash2to1`, `Hash4to1`, `Hash3Cap`, `MerkleHash8` — via the real
    /// in-circuit gadget. See `check_algebraic` below, which is the authority.
    ///
    /// (Corrected 2026-07-16: this previously listed "`Hash` sponge" as UNSUPPORTED, contradicting
    /// `check_algebraic`, which returns `Ok(())` for it. The stale claim mattered: it is the same
    /// story `dregg-dsl-runtime/src/dsl_plonky3.rs`'s duplicate `DslP3Air` tells about ITSELF — where
    /// it is TRUE — and it is why the differential harness skips membership coverage citing "DslP3Air
    /// cannot inline Poseidon2". The DSL membership circuit uses `ConstraintExpr::Hash`
    /// (`dsl/membership.rs:17`), which THIS interpreter accepts.)
    pub fn try_from_dsl(dsl: &DslCircuit) -> Result<Self, DslP3Error> {
        for (i, c) in dsl.descriptor.constraints.iter().enumerate() {
            check_algebraic(c, i)?;
        }
        // THE STANDING CONTROL (runs on every prove AND every verify, not an
        // injection anyone has to remember to fire): the number of Poseidon2 aux
        // blocks this AIR ALLOCATES must equal the number of hash forms the
        // descriptor CONTAINS. `is_hash` is deliberately shallow because it drives
        // allocation; `hash_forms_deep` counts the same forms wherever they sit. A
        // mismatch means a hash form exists that gets no aux block — i.e. a
        // constraint that would lower to nothing. Refuse instead of emitting it.
        //
        // `check_algebraic` above already rejects every shape that can cause this
        // today; this counter is the form-agnostic backstop, so a NEW wrapper form
        // added to `ConstraintExpr` reds here rather than silently erasing.
        let allocated = hash_count(dsl);
        let contained: usize = dsl.descriptor.constraints.iter().map(hash_forms_deep).sum();
        if allocated != contained {
            return Err(DslP3Error::ErasedConstraint {
                index: dsl
                    .descriptor
                    .constraints
                    .iter()
                    .position(|c| hash_forms_deep(c) != usize::from(is_hash(c)))
                    .unwrap_or(0),
                detail: "a hash form is nested inside a wrapper, so it would receive no \
                         Poseidon2 aux block and lower to assert_zero(0)",
            });
        }
        Ok(Self {
            descriptor: dsl.descriptor.clone(),
            base_width: dsl.descriptor.trace_width,
            full_width: air_width(dsl),
            interior_aux_base: interior_aux_base(dsl),
        })
    }
}

/// Errors from the DSL→p3 migration path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DslP3Error {
    /// The descriptor contains a constraint form that has no symbolic p3
    /// arithmetization in this module (hash / merkle / lookup). Route such a
    /// circuit through the dedicated arithmetized AIRs instead.
    NonAlgebraicConstraint { index: usize, form: &'static str },
    /// The descriptor contains a constraint that this module would emit as a
    /// TRIVIALLY-SATISFIED expression — a hash form nested inside a
    /// `Gated`/`InvertedGated`/`Squared` wrapper, which gets no Poseidon2 aux block
    /// and folds through `eval_expr` to `assert_zero(selector · 0)`.
    ///
    /// ⚑ This is a REFUSAL, not a gate-off. Before 2026-07-30 the same descriptor
    /// lowered silently and the wrapped constraint was ERASED: satisfied by every
    /// assignment, including with the selector set to 1. A constraint form this
    /// module cannot emit must be an error, never a no-op.
    ErasedConstraint { index: usize, detail: &'static str },
    /// The real Plonky3 verifier rejected the proof.
    VerificationFailed { reason: String },
}

impl core::fmt::Display for DslP3Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DslP3Error::NonAlgebraicConstraint { index, form } => write!(
                f,
                "constraint {index} is non-algebraic ({form}); use the arithmetized p3 AIR for it"
            ),
            DslP3Error::ErasedConstraint { index, detail } => write!(
                f,
                "constraint {index} would be ERASED by this lowering ({detail}); \
                 emit the hash ungated, or route the descriptor through the IR2 \
                 chip-lookup lowering, which honours selector-muxed hash sites"
            ),
            DslP3Error::VerificationFailed { reason } => {
                write!(f, "p3 verification failed: {reason}")
            }
        }
    }
}

impl std::error::Error for DslP3Error {}

/// Confirm a constraint is supported by this p3 AIR. Pure-algebraic forms and
/// the Poseidon2 hash forms (`Hash`/`Hash2to1`/`Hash4to1`) are supported
/// (hashes via the real in-circuit `poseidon2_permute_expr` gadget). `Hash` is
/// the single-permutation `hash_fact` sponge (predicate + ≤4 terms, leaf
/// domain separation); it consumes one Poseidon2 aux block exactly like
/// `Hash2to1`/`Hash4to1`. `MerkleHash` (position-indexed) routes through
/// the Lean-emitted IR2 membership descriptor, and `Lookup` requires the LogUp bus
/// (`lean_lookup_air`); both are surfaced as errors rather than silently
/// dropped.
fn check_algebraic(c: &ConstraintExpr, index: usize) -> Result<(), DslP3Error> {
    check_algebraic_inner(c, index, false)
}

/// `wrapped` is true once we have descended through a `Gated`/`InvertedGated`/
/// `Squared`. A hash form found there is REFUSED (2026-07-30): it would receive no
/// Poseidon2 aux block and `eval_expr` returns `AB::Expr::ZERO` for every hash form,
/// so the emitted constraint would be `assert_zero(selector · 0)` — satisfied by
/// every assignment. That is erasure, not gating, and it silently deleted the
/// shielded-spend nullifier binding (C4) from the deployed hiding verifier.
///
/// ⚑ SUBSTRATE: this is a refusal in a LOWERING. It authors no constraint — the
/// repair for a descriptor that trips it is to emit the hash ungated (into a column
/// carried on every row) or to route the descriptor through the IR2 chip-lookup
/// lowering, which does honour selector-muxed hash sites. The Lean algebraic
/// emitter cannot express this shape at all: `Dregg2.Exec.CircuitEmit`'s
/// `EmittedConstraintA` has `gated`/`invertedGated`/`squared` but NO hash
/// constructor — the hash forms live in the separate `EmittedConstraintM` /
/// `HashForm` inductives. A nested hash is therefore only reachable from a
/// Rust-authored descriptor.
fn check_algebraic_inner(
    c: &ConstraintExpr,
    index: usize,
    wrapped: bool,
) -> Result<(), DslP3Error> {
    if wrapped && is_hash(c) {
        return Err(DslP3Error::ErasedConstraint {
            index,
            detail: "a Hash/Hash2to1/Hash4to1/Hash3Cap/MerkleHash8 nested inside a \
                     Gated/InvertedGated/Squared wrapper",
        });
    }
    match c {
        ConstraintExpr::Equality { .. }
        | ConstraintExpr::Multiplication { .. }
        | ConstraintExpr::Binary { .. }
        | ConstraintExpr::PiBinding { .. }
        | ConstraintExpr::Transition { .. }
        | ConstraintExpr::Polynomial { .. }
        | ConstraintExpr::ConditionalNonzero { .. }
        | ConstraintExpr::AtLeastOne { .. }
        | ConstraintExpr::Hash { .. }
        | ConstraintExpr::Hash2to1 { .. }
        | ConstraintExpr::Hash4to1 { .. }
        | ConstraintExpr::Hash3Cap { .. }
        | ConstraintExpr::MerkleHash8 { .. } => Ok(()),
        ConstraintExpr::Gated { inner, .. }
        | ConstraintExpr::InvertedGated { inner, .. }
        | ConstraintExpr::Squared { inner } => check_algebraic_inner(inner, index, true),
        ConstraintExpr::MerkleHash { .. } => Err(DslP3Error::NonAlgebraicConstraint {
            index,
            form: "MerkleHash (use the Lean-emitted IR2 descriptor for position-indexed Merkle hashing)",
        }),
        ConstraintExpr::Lookup { .. } => Err(DslP3Error::NonAlgebraicConstraint {
            index,
            form: "Lookup (route through the LogUp bus / lean_lookup_air)",
        }),
        // Cross-row / PI-seeded running hashes absorb a Poseidon2 input drawn from
        // the `next` window (chain) or a public input (seed). The single-permutation
        // aux-block model here only handles hashes whose inputs are all in the `local`
        // window, so these forms route through the native `crate::stark` prover (the
        // path the live `DslCircuitDfaVerifier` uses) rather than the Plonky3 batch AIR.
        ConstraintExpr::ChainedHash2to1 { .. } => Err(DslP3Error::NonAlgebraicConstraint {
            index,
            form: "ChainedHash2to1 (cross-row running hash; route through crate::stark)",
        }),
        ConstraintExpr::SeedHash2to1 { .. } => Err(DslP3Error::NonAlgebraicConstraint {
            index,
            form: "SeedHash2to1 (PI-seeded running hash; route through crate::stark)",
        }),
        // `TableFunction` is a genuine low-degree polynomial, but its symbolic
        // expansion (bivariate Lagrange interpolation) is not yet emitted into the
        // Plonky3 `AB::Expr` path; route it through the native `crate::stark` prover
        // (the path the live `DslCircuitDfaVerifier` uses).
        ConstraintExpr::TableFunction { .. } => Err(DslP3Error::NonAlgebraicConstraint {
            index,
            form: "TableFunction (bivariate-interpolation table; route through crate::stark)",
        }),
    }
}

/// Whether a constraint is a Poseidon2 hash form needing one permutation aux
/// block (Hash sponge / Hash2to1 / Hash4to1 — the single-permutation hashing
/// forms). All three resolve to ONE Poseidon2 permutation, so each consumes
/// exactly one aux block.
fn is_hash(c: &ConstraintExpr) -> bool {
    matches!(
        c,
        ConstraintExpr::Hash { .. }
            | ConstraintExpr::Hash2to1 { .. }
            | ConstraintExpr::Hash4to1 { .. }
            | ConstraintExpr::Hash3Cap { .. }
            | ConstraintExpr::MerkleHash8 { .. }
    )
}

/// Number of hash forms in a constraint TREE, including any nested under a
/// `Gated`/`InvertedGated`/`Squared` wrapper — the forms [`is_hash`] does NOT see
/// because it is deliberately shallow (it drives aux-block ALLOCATION, and only a
/// top-level hash gets one).
///
/// The gap between this and [`is_hash`] IS the erasure: a nested hash is counted
/// here, not there, so `contained != allocated` and [`DslP3Air::try_from_dsl`]
/// refuses. Keep this recursive over every wrapper form `ConstraintExpr` ever
/// gains — that is what makes the control form-agnostic.
fn hash_forms_deep(c: &ConstraintExpr) -> usize {
    if is_hash(c) {
        return 1;
    }
    match c {
        ConstraintExpr::Gated { inner, .. }
        | ConstraintExpr::InvertedGated { inner, .. }
        | ConstraintExpr::Squared { inner } => hash_forms_deep(inner),
        _ => 0,
    }
}

/// Number of Poseidon2 hash constraints in a descriptor (= number of aux blocks).
fn hash_count(dsl: &DslCircuit) -> usize {
    dsl.descriptor
        .constraints
        .iter()
        .filter(|c| is_hash(c))
        .count()
}

/// An interior-row boundary `trace[k][col] == target` where `k` is an absolute
/// row index `> 0` (so it has no p3 first/last selector). `target` is either a
/// public input (`Some(pi_index)`) or a fixed value (`None` ⇒ use `fixed`).
#[derive(Clone, Debug)]
struct InteriorBoundary {
    row: usize,
    // Carried for the interior-boundary constraint emission; currently only the
    // boundary count drives the aux-column width (`interior_aux_cols`).
    #[allow(dead_code)]
    col: usize,
    #[allow(dead_code)]
    pi_index: Option<usize>,
    #[allow(dead_code)]
    fixed: BabyBear,
}

/// Collect the interior-row boundaries (absolute index `> 0`). `First`, `Last`,
/// and `Index(0)` are NOT interior (they map to p3 row selectors).
fn interior_boundaries(dsl: &DslCircuit) -> Vec<InteriorBoundary> {
    let mut out = Vec::new();
    for b in &dsl.descriptor.boundaries {
        match b {
            BoundaryDef::PiBinding {
                row: BoundaryRow::Index(k),
                col,
                pi_index,
            } if *k != 0 => {
                out.push(InteriorBoundary {
                    row: *k,
                    col: *col,
                    pi_index: Some(*pi_index),
                    fixed: BabyBear::ZERO,
                });
            }
            BoundaryDef::Fixed {
                row: BoundaryRow::Index(k),
                col,
                value,
            } if *k != 0 => {
                out.push(InteriorBoundary {
                    row: *k,
                    col: *col,
                    pi_index: None,
                    fixed: *value,
                });
            }
            _ => {}
        }
    }
    out
}

/// The interior-row selector aux block: one shared `row_idx` counter column,
/// then 2 columns per interior boundary (`inv`, `is_k`) for the IsZero gadget.
/// Sits AFTER the hash aux blocks. Empty (0 columns) when there are no interior
/// boundaries — so circuits without them keep their exact previous width.
fn interior_aux_cols(dsl: &DslCircuit) -> usize {
    let n = interior_boundaries(dsl).len();
    if n == 0 { 0 } else { 1 + 2 * n }
}

/// Base offset (after base columns + hash aux blocks) where the interior-row
/// selector aux block begins.
fn interior_aux_base(dsl: &DslCircuit) -> usize {
    dsl.descriptor.trace_width + hash_count(dsl) * POSEIDON2_PERM_AUX_COLS
}

/// The FULL p3 trace width: base columns + one Poseidon2 aux block per hash +
/// the interior-row selector aux block (counter + per-boundary IsZero witness).
fn air_width(dsl: &DslCircuit) -> usize {
    interior_aux_base(dsl) + interior_aux_cols(dsl)
}

/// Build the 16-wide Poseidon2 input state (as `AB::Expr`) for a hash form,
/// matching the concrete `hash_2_to_1` / `hash_4_to_1` / `hash_fact` input-state
/// construction (arity/domain tags at the documented capacity slots).
fn hash_input_state<AB: AirBuilder>(
    c: &ConstraintExpr,
    local: &[AB::Var],
) -> [AB::Expr; POSEIDON2_WIDTH] {
    let mut st: [AB::Expr; POSEIDON2_WIDTH] = core::array::from_fn(|_| AB::Expr::ZERO);
    match c {
        // `hash_fact(predicate, terms)`: state[0]=predicate, state[1..1+|terms|]=
        // terms (≤4 absorbed at rate positions 1..5), capacity carries the leaf
        // domain separation tags state[5]=0xFACF and state[6]=1. Mirrors
        // `crate::poseidon2::hash_fact` exactly.
        ConstraintExpr::Hash { input_cols, .. } => {
            st[0] = local[input_cols[0]].into();
            let nterms = (input_cols.len() - 1).min(4);
            for k in 0..nterms {
                st[1 + k] = local[input_cols[1 + k]].into();
            }
            st[5] = AB::Expr::from_u64(0xFACF);
            st[6] = AB::Expr::ONE;
        }
        ConstraintExpr::Hash2to1 {
            input_col_a,
            input_col_b,
            ..
        } => {
            st[0] = local[*input_col_a].into();
            st[1] = local[*input_col_b].into();
            st[4] = AB::Expr::from_u64(2); // arity tag (matches hash_2_to_1)
        }
        ConstraintExpr::Hash4to1 { input_cols, .. } => {
            st[0] = local[input_cols[0]].into();
            st[1] = local[input_cols[1]].into();
            st[2] = local[input_cols[2]].into();
            st[3] = local[input_cols[3]].into();
            st[4] = AB::Expr::from_u64(4); // arity tag (matches hash_4_to_1)
        }
        // `cap_node(left, right)` = `cap_chip_absorb([FACT_MARK, left, right])`: the arity-3
        // rate-8 chip absorb — FACT_MARK at rate lane 0, children at 1/2, length tag 3 at
        // lane 4. Mirrors `crate::cap_root::cap_node` byte-for-byte.
        ConstraintExpr::Hash3Cap {
            left_col,
            right_col,
            ..
        } => {
            st[0] = AB::Expr::from_u64(crate::cap_root::CAP_FACT_MARK as u64);
            st[1] = local[*left_col].into();
            st[2] = local[*right_col].into();
            st[4] = AB::Expr::from_u64(3); // arity tag (matches cap_chip_absorb len=3)
        }
        // `cap_node8(L8, R8)` = the arity-16 `node8` compression: the 16-wide input state is
        // exactly `L8 ‖ R8` seeded into all 16 lanes (`chip_absorb_all_lanes(16, L8‖R8)` puts
        // ins[0..16] into state[0..16] with NO tag lane — node8 seeds every lane with a genuine
        // input). All 8 output lanes are read by the caller via `poseidon2_permute_expr_lanes`.
        ConstraintExpr::MerkleHash8 {
            left_cols,
            right_cols,
            ..
        } => {
            for i in 0..8 {
                st[i] = local[left_cols[i]].into();
                st[8 + i] = local[right_cols[i]].into();
            }
        }
        _ => unreachable!(
            "hash_input_state only called on Hash/Hash2to1/Hash4to1/Hash3Cap/MerkleHash8"
        ),
    }
    st
}

/// The output column a hash form binds its digest to.
fn hash_output_col(c: &ConstraintExpr) -> usize {
    match c {
        ConstraintExpr::Hash { output_col, .. }
        | ConstraintExpr::Hash2to1 { output_col, .. }
        | ConstraintExpr::Hash4to1 { output_col, .. }
        | ConstraintExpr::Hash3Cap { output_col, .. } => *output_col,
        _ => unreachable!("hash_output_col only called on Hash/Hash2to1/Hash4to1/Hash3Cap"),
    }
}

/// The concrete 16-wide Poseidon2 input state for witness generation, matching
/// [`hash_input_state`].
fn hash_input_state_concrete(c: &ConstraintExpr, row: &[BabyBear]) -> [BabyBear; POSEIDON2_WIDTH] {
    let mut st = [BabyBear::ZERO; POSEIDON2_WIDTH];
    match c {
        ConstraintExpr::Hash { input_cols, .. } => {
            st[0] = row[input_cols[0]];
            let nterms = (input_cols.len() - 1).min(4);
            for k in 0..nterms {
                st[1 + k] = row[input_cols[1 + k]];
            }
            st[5] = BabyBear::new(0xFACF);
            st[6] = BabyBear::ONE;
        }
        ConstraintExpr::Hash2to1 {
            input_col_a,
            input_col_b,
            ..
        } => {
            st[0] = row[*input_col_a];
            st[1] = row[*input_col_b];
            st[4] = BabyBear::new(2);
        }
        ConstraintExpr::Hash4to1 { input_cols, .. } => {
            st[0] = row[input_cols[0]];
            st[1] = row[input_cols[1]];
            st[2] = row[input_cols[2]];
            st[3] = row[input_cols[3]];
            st[4] = BabyBear::new(4);
        }
        ConstraintExpr::Hash3Cap {
            left_col,
            right_col,
            ..
        } => {
            // `cap_node` seeding: FACT_MARK at lane 0, children at 1/2, length tag 3 at lane 4.
            st[0] = BabyBear::new(crate::cap_root::CAP_FACT_MARK);
            st[1] = row[*left_col];
            st[2] = row[*right_col];
            st[4] = BabyBear::new(3);
        }
        // node8 concrete seeding: `L8 ‖ R8` into all 16 lanes (byte-identical to the arity-16
        // `chip_absorb_all_lanes` gather), so the aux witness this fills matches the
        // symbolic `hash_input_state` above.
        ConstraintExpr::MerkleHash8 {
            left_cols,
            right_cols,
            ..
        } => {
            for i in 0..8 {
                st[i] = row[left_cols[i]];
                st[8 + i] = row[right_cols[i]];
            }
        }
        _ => unreachable!(),
    }
    st
}

/// Symbolically evaluate an algebraic constraint to an `AB::Expr`, mirroring
/// `ConstraintExpr::evaluate_with_tables` term-for-term. Panics only on a
/// non-algebraic form, which `try_from_dsl` has already rejected.
fn eval_expr<AB: AirBuilder>(c: &ConstraintExpr, local: &[AB::Var], next: &[AB::Var]) -> AB::Expr {
    // helper closures
    let col = |i: usize| -> AB::Expr { local[i].into() };
    let one = AB::Expr::ONE;
    match c {
        ConstraintExpr::Equality { col_a, col_b } => col(*col_a) - col(*col_b),
        ConstraintExpr::Multiplication { a, b, output } => col(*a) * col(*b) - col(*output),
        ConstraintExpr::Binary { col: cc } => col(*cc) * (col(*cc) - one.clone()),
        ConstraintExpr::PiBinding { .. } => {
            // PiBinding is handled as a boundary in this module's `eval` (it
            // needs `public_values`, not available here). The per-row form is a
            // no-op; the boundary form pins the cell. Returning ZERO keeps the
            // constraint vector aligned without double-counting.
            AB::Expr::ZERO
        }
        ConstraintExpr::Transition {
            next_col,
            local_col,
        } => {
            // Transition references `next`; emit (next[next_col] - local[local_col]).
            let n: AB::Expr = next[*next_col].into();
            n - col(*local_col)
        }
        ConstraintExpr::Polynomial { terms } => {
            let mut sum = AB::Expr::ZERO;
            for term in terms {
                let mut prod: AB::Expr = lift::<AB>(term.coeff);
                for &ci in &term.col_indices {
                    prod *= col(ci);
                }
                sum += prod;
            }
            sum
        }
        ConstraintExpr::Gated {
            selector_col,
            inner,
        } => col(*selector_col) * eval_expr::<AB>(inner, local, next),
        ConstraintExpr::InvertedGated {
            selector_col,
            inner,
        } => (one.clone() - col(*selector_col)) * eval_expr::<AB>(inner, local, next),
        ConstraintExpr::Squared { inner } => {
            let v = eval_expr::<AB>(inner, local, next);
            v.clone() * v
        }
        ConstraintExpr::ConditionalNonzero {
            selector_col,
            value_col,
            inverse_col,
        } => col(*selector_col) * (col(*value_col) * col(*inverse_col) - one.clone()),
        ConstraintExpr::AtLeastOne { flag_cols } => {
            let mut product = one.clone();
            for &cc in flag_cols {
                product *= one.clone() - col(cc);
            }
            product
        }
        // ⚑ FAIL CLOSED, not silently zero (2026-07-30). These arms returned
        // `AB::Expr::ZERO`, and that value was NOT unreachable: a hash nested under
        // `Gated`/`InvertedGated`/`Squared` folded straight through here, so the
        // emitted constraint was `assert_zero(selector · 0)` — trivially true for
        // every assignment. That erased the shielded-spend nullifier binding from
        // the deployed verifier.
        //
        // Every one of these forms is now REFUSED at `check_algebraic` at ANY depth
        // (top-level hashes are emitted as Poseidon2 aux blocks in `eval` before the
        // catch-all ever calls this function), so reaching here is a lowering bug,
        // not an input. Abort loudly rather than emit a satisfied-by-everything
        // constraint.
        ConstraintExpr::Hash { .. }
        | ConstraintExpr::Hash2to1 { .. }
        | ConstraintExpr::Hash4to1 { .. }
        | ConstraintExpr::Hash3Cap { .. }
        | ConstraintExpr::MerkleHash8 { .. }
        | ConstraintExpr::MerkleHash { .. }
        | ConstraintExpr::Lookup { .. }
        | ConstraintExpr::ChainedHash2to1 { .. }
        | ConstraintExpr::SeedHash2to1 { .. }
        | ConstraintExpr::TableFunction { .. } => unreachable!(
            "a non-algebraic form reached eval_expr; try_from_dsl must have refused it \
             (DslP3Error::ErasedConstraint / NonAlgebraicConstraint)"
        ),
    }
}

/// Lift one of our `BabyBear` field elements into an `AB::Expr`. BabyBear values
/// are `< p < 2^31`, so `from_u64` is canonical and exact.
fn lift<AB: AirBuilder>(v: BabyBear) -> AB::Expr {
    AB::Expr::from_u64(v.0 as u64)
}

impl<F: PrimeCharacteristicRing + Sync> BaseAir<F> for DslP3Air {
    fn width(&self) -> usize {
        self.full_width
    }

    fn num_public_values(&self) -> usize {
        self.descriptor.public_input_count
    }
}

/// (local row vars, next row vars, public values) extracted at the start of `eval`.
type EvalRows<AB> = (
    Vec<<AB as AirBuilder>::Var>,
    Vec<<AB as AirBuilder>::Var>,
    Vec<<AB as AirBuilder>::Expr>,
);

impl<AB: AirBuilder> Air<AB> for DslP3Air
where
    AB::F: PrimeField32,
{
    fn eval(&self, builder: &mut AB) {
        let (local, next, public_values): EvalRows<AB> = {
            let main = builder.main();
            let local: Vec<AB::Var> = main.current_slice().to_vec();
            let next: Vec<AB::Var> = main.next_slice().to_vec();
            let public_values: Vec<AB::Expr> =
                builder.public_values().iter().map(|&v| v.into()).collect();
            (local, next, public_values)
        };

        // ---- transition / per-row / hash constraints ----
        // Hash forms (Hash2to1/Hash4to1) consume a Poseidon2 aux block each, laid
        // out after the base columns in declaration order.
        let mut hash_block = 0usize;
        for c in &self.descriptor.constraints {
            match c {
                // PiBinding as a row-constraint binds local[col] to a public
                // value on EVERY row (the DSL evaluates it per-row). Mirror that.
                ConstraintExpr::PiBinding { col, pi_index } => {
                    let lv: AB::Expr = local[*col].into();
                    let pv: AB::Expr = public_values[*pi_index].clone();
                    builder.assert_zero(lv - pv);
                }
                // Poseidon2 hash: real in-circuit permutation against this hash's
                // aux block; digest bound to the output column.
                c if is_hash(c) => {
                    let base = self.base_width + hash_block * POSEIDON2_PERM_AUX_COLS;
                    let aux: Vec<AB::Var> = local[base..base + POSEIDON2_PERM_AUX_COLS].to_vec();
                    let input = hash_input_state::<AB>(c, &local);
                    match c {
                        // Multi-output node8: bind ALL 8 genuine permutation output lanes to
                        // the 8 parent columns (the ~124-bit faithful 8-felt node hash). The
                        // lanes are 8 DISTINCT field elements (the final permutation state),
                        // NOT eight copies of lane 0 — the full-width collision floor.
                        ConstraintExpr::MerkleHash8 { output_cols, .. } => {
                            let lanes = poseidon2_permute_expr_lanes::<AB>(builder, input, &aux);
                            for i in 0..8 {
                                let out: AB::Expr = local[output_cols[i]].into();
                                builder.assert_eq(lanes[i].clone(), out);
                            }
                        }
                        // Single-output hashes squeeze lane 0 only.
                        _ => {
                            let digest = poseidon2_permute_expr::<AB>(builder, input, &aux);
                            let out: AB::Expr = local[hash_output_col(c)].into();
                            builder.assert_eq(digest, out);
                        }
                    }
                    hash_block += 1;
                }
                // Any constraint that references `next` must be gated to
                // skip the wrap-around at the last row.
                c if references_next(c) => {
                    let e = eval_expr::<AB>(c, &local, &next);
                    builder.when_transition().assert_zero(e);
                }
                c => {
                    let e = eval_expr::<AB>(c, &local, &next);
                    builder.assert_zero(e);
                }
            }
        }

        // ---- boundary constraints (First / Last / Index(0)) ----
        // Interior-row boundaries (`Index(k)`, k>0) are handled by the
        // interior-row selector block below — skip them here.
        for bdef in &self.descriptor.boundaries {
            match bdef {
                BoundaryDef::PiBinding { row, col, pi_index } => {
                    if matches!(row, BoundaryRow::Index(k) if *k != 0) {
                        continue;
                    }
                    let lv: AB::Expr = local[*col].into();
                    let pv: AB::Expr = public_values[*pi_index].clone();
                    apply_boundary::<AB>(builder, *row, lv - pv);
                }
                BoundaryDef::Fixed { row, col, value } => {
                    if matches!(row, BoundaryRow::Index(k) if *k != 0) {
                        continue;
                    }
                    let lv: AB::Expr = local[*col].into();
                    let fv: AB::Expr = lift::<AB>(*value);
                    apply_boundary::<AB>(builder, *row, lv - fv);
                }
            }
        }

        // ---- interior-row boundaries via a sound row-indicator gadget ----
        //
        // p3 has no selector for an arbitrary interior row `k`. We add ONE shared
        // `row_idx` counter column (pinned `row_idx == 0` on the first row, and
        // `next.row_idx == row_idx + 1` on every transition — so `row_idx` is the
        // genuine absolute row index), plus, per interior boundary, an
        // IsZero(row_idx - k) gadget (`inv`, `is_k`):
        //
        //   is_k * (row_idx - k)              == 0   (is_k ⇒ row == k)
        //   (row_idx - k) * inv + is_k - 1    == 0   (row != k ⇒ is_k = 0; row == k ⇒ is_k = 1)
        //
        // These two force `is_k == [row_idx == k]` EXACTLY (standard IsZero), so
        // the binding `is_k * (col - target) == 0` fires on exactly row k and is
        // vacuous elsewhere. The counter makes `row_idx` unforgeable, so a prover
        // cannot dodge the binding by mislabelling rows.
        let interiors = interior_boundaries_from_descriptor(&self.descriptor);
        if !interiors.is_empty() {
            let aux_base = self.interior_aux_base;
            let row_idx: AB::Expr = local[aux_base].into();
            let next_row_idx: AB::Expr = next[aux_base].into();

            // Counter pins: first row 0, +1 each transition.
            builder.when_first_row().assert_zero(row_idx.clone());
            builder
                .when_transition()
                .assert_zero(next_row_idx - row_idx.clone() - AB::Expr::ONE);

            for (i, ib) in interiors.iter().enumerate() {
                let inv: AB::Expr = local[aux_base + 1 + 2 * i].into();
                let is_k: AB::Expr = local[aux_base + 2 + 2 * i].into();
                let diff = row_idx.clone() - AB::Expr::from_u64(ib.row as u64);

                // IsZero gadget.
                builder.assert_zero(is_k.clone() * diff.clone());
                builder.assert_zero(diff * inv + is_k.clone() - AB::Expr::ONE);

                // The binding, active only on row k.
                let target: AB::Expr = match ib.pi_index {
                    Some(p) => public_values[p].clone(),
                    None => lift::<AB>(ib.fixed),
                };
                let cell: AB::Expr = local[ib.col].into();
                builder.assert_zero(is_k * (cell - target));
            }
        }
    }
}

/// Interior-row boundary, recomputed inside `eval` from the stored descriptor
/// (mirrors [`InteriorBoundary`]; kept here so `eval` needs no extra fields).
struct EvalInteriorBoundary {
    row: usize,
    col: usize,
    pi_index: Option<usize>,
    fixed: BabyBear,
}

fn interior_boundaries_from_descriptor(
    desc: &crate::dsl::circuit::CircuitDescriptor,
) -> Vec<EvalInteriorBoundary> {
    let mut out = Vec::new();
    for b in &desc.boundaries {
        match b {
            BoundaryDef::PiBinding {
                row: BoundaryRow::Index(k),
                col,
                pi_index,
            } if *k != 0 => {
                out.push(EvalInteriorBoundary {
                    row: *k,
                    col: *col,
                    pi_index: Some(*pi_index),
                    fixed: BabyBear::ZERO,
                });
            }
            BoundaryDef::Fixed {
                row: BoundaryRow::Index(k),
                col,
                value,
            } if *k != 0 => {
                out.push(EvalInteriorBoundary {
                    row: *k,
                    col: *col,
                    pi_index: None,
                    fixed: *value,
                });
            }
            _ => {}
        }
    }
    out
}

/// Whether a constraint reads the `next` row (must be transition-gated).
fn references_next(c: &ConstraintExpr) -> bool {
    match c {
        ConstraintExpr::Transition { .. } => true,
        ConstraintExpr::Gated { inner, .. }
        | ConstraintExpr::InvertedGated { inner, .. }
        | ConstraintExpr::Squared { inner } => references_next(inner),
        _ => false,
    }
}

/// Apply a boundary expression at a `First` / `Last` / `Index(0)` row position.
///
/// `First`/`Last`/`Index(0)` map to p3's first/last-row selectors. Interior
/// boundaries (`Index(k)`, k>0) are NOT routed here — `eval` skips them and
/// enforces them via the sound row-indicator gadget (counter + IsZero) instead.
/// Reaching the `Index(_>0)` arm would be a caller bug; we no-op (assert 0) so
/// no spurious over-constraint is emitted.
fn apply_boundary<AB: AirBuilder>(builder: &mut AB, row: BoundaryRow, expr: AB::Expr) {
    match row {
        BoundaryRow::First => {
            builder.when_first_row().assert_zero(expr);
        }
        BoundaryRow::Last => {
            builder.when_last_row().assert_zero(expr);
        }
        BoundaryRow::Index(0) => {
            builder.when_first_row().assert_zero(expr);
        }
        BoundaryRow::Index(_) => {
            let _ = expr;
            builder.assert_zero(AB::Expr::ZERO);
        }
    }
}

/// Prove a DSL circuit through the **audited Plonky3 prover** (`p3-batch-stark`).
///
/// `trace` is the witness (row-major `Vec<Vec<BabyBear>>`, width =
/// `descriptor.trace_width`, power-of-two height). `public_inputs` are the
/// circuit's public values (length = `descriptor.public_input_count`).
///
/// Returns the p3 proof on success. The proof is self-verified before return
/// (matching the other migrated AIRs), so a returned proof is one the audited
/// verifier accepts.
pub fn prove_dsl_p3(
    dsl: &DslCircuit,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
) -> Result<DslP3Proof, DslP3Error> {
    let air = DslP3Air::try_from_dsl(dsl)?;

    let config = create_config();
    // Extend each base trace row with the Poseidon2 aux blocks the hash
    // constraints' in-circuit permutation reads.
    let full_trace = extend_trace_with_hash_aux(dsl, trace);
    let matrix = to_matrix(&full_trace);
    let pis: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();

    let instances = vec![StarkInstance {
        air: &air,
        trace: &matrix,
        public_values: pis.clone(),
    }];
    let prover_data = ProverData::from_instances(&config, &instances);
    let common = &prover_data.common;
    let proof = prove_batch(&config, &instances, &prover_data);

    // Self-verify (the audited verifier must accept what we just proved).
    let airs = vec![air];
    let pvs = vec![pis];
    verify_batch(&config, &airs, &proof, &pvs, common).map_err(|e| {
        DslP3Error::VerificationFailed {
            reason: format!("{e:?}"),
        }
    })?;
    Ok(proof)
}

/// Verify a DSL circuit proof through the **audited Plonky3 verifier**
/// (`p3-batch-stark`).
///
/// The verifier reconstructs the batch `CommonData` (lookup/preprocessed shape)
/// from the AIR plus the per-instance degree bits carried in the proof — it does
/// NOT need the prover's witness. This is the genuine standalone-verifier path.
pub fn verify_dsl_p3(
    dsl: &DslCircuit,
    proof: &DslP3Proof,
    public_inputs: &[BabyBear],
) -> Result<(), DslP3Error> {
    let air = DslP3Air::try_from_dsl(dsl)?;

    let config = create_config();
    let pis: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();

    let airs = vec![air];
    let pvs = vec![pis];

    // Reconstruct CommonData from AIRs + the proof's degree bits (witness-free).
    let common = ProverData::from_airs_and_degrees(&config, &airs, &proof.degree_bits).common;

    verify_batch(&config, &airs, proof, &pvs, &common).map_err(|e| DslP3Error::VerificationFailed {
        reason: format!("{e:?}"),
    })
}

/// Extend each base-width trace row with (1) the Poseidon2 intermediate-state
/// aux columns the hash constraints' in-circuit permutation gadget reads (in the
/// same declaration order `eval` consumes them), then (2) the interior-row
/// selector aux block: a `row_idx` counter (= the absolute row index) followed
/// by per-interior-boundary `(inv, is_k)` IsZero witnesses. A descriptor with
/// neither hashes nor interior boundaries returns the trace unchanged.
fn extend_trace_with_hash_aux(dsl: &DslCircuit, trace: &[Vec<BabyBear>]) -> Vec<Vec<BabyBear>> {
    let hashes: Vec<&ConstraintExpr> = dsl
        .descriptor
        .constraints
        .iter()
        .filter(|c| is_hash(c))
        .collect();
    let interiors = interior_boundaries(dsl);
    if hashes.is_empty() && interiors.is_empty() {
        return trace.to_vec();
    }
    trace
        .iter()
        .enumerate()
        .map(|(r, row)| {
            let mut full = row.clone();
            // (1) Poseidon2 hash aux blocks (declaration order).
            for c in &hashes {
                let input = hash_input_state_concrete(c, row);
                full.extend(poseidon2_permute_aux_witness(input));
            }
            // (2) interior-row selector block: counter + per-boundary IsZero.
            if !interiors.is_empty() {
                full.push(BabyBear::new(r as u32)); // row_idx counter
                for ib in &interiors {
                    let diff = BabyBear::new(r as u32) - BabyBear::new(ib.row as u32);
                    if diff == BabyBear::ZERO {
                        full.push(BabyBear::ZERO); // inv (unused on the matching row)
                        full.push(BabyBear::ONE); // is_k = 1
                    } else {
                        full.push(diff.inverse().expect("nonzero diff is invertible")); // inv = (row_idx - k)^{-1}
                        full.push(BabyBear::ZERO); // is_k = 0
                    }
                }
            }
            full
        })
        .collect()
}

/// Convert a `Vec<Vec<BabyBear>>` trace to a p3 `RowMajorMatrix`.
fn to_matrix(trace: &[Vec<BabyBear>]) -> RowMajorMatrix<P3BabyBear> {
    let width = trace[0].len();
    let values: Vec<P3BabyBear> = trace
        .iter()
        .flat_map(|row| row.iter().map(|&v| to_p3(v)))
        .collect();
    RowMajorMatrix::new(values, width)
}

// ============================================================================
// Zero-knowledge (hiding) seam: route a `DslCircuit` through the statistically-
// ZK uni-STARK path (`crate::stark_zk::create_zk_config` over `HidingFriPcs`).
// ============================================================================
//
// `prove_dsl_p3`/`verify_dsl_p3` above ride `p3-batch-stark` over the NON-hiding
// `DreggStarkConfig` — succinct + sound but the FRI openings reveal witness
// evaluations. For the privacy lane (shielded actions) we need the SAME
// descriptor-driven `DslP3Air`, but proved with the hiding PCS so the openings
// reveal nothing about the witness beyond the public inputs.
//
// The clean weld: `DslP3Air` already implements `p3_air::Air<AB>` with exactly
// the bounds (`AB: AirBuilder, AB::F: PrimeField32`) that `crate::stark_zk`'s
// retired Merkle AIR did, and `prove_zk` runs THAT air through
// `p3_uni_stark::{prove,verify}` over the hiding config. So a `DslP3Air` rides
// the identical hiding uni-STARK entry points — no AIR change, just the config.
//
// This is the shielded lane's only dependency on a shared circuit file; it is
// additive (no existing path touched) and reuses the internal aux-extension +
// AIR builder so the hiding proof binds the SAME constraints the audited
// non-hiding path does.
#[cfg(feature = "plonky3")]
pub use zk_seam::*;

#[cfg(feature = "plonky3")]
mod zk_seam {
    use super::{DslP3Air, DslP3Error, extend_trace_with_hash_aux, to_matrix};
    use crate::dsl::circuit::DslCircuit;
    use crate::field::BabyBear;
    use crate::plonky3_prover::to_p3;
    use crate::stark_zk::{DreggZkProof, create_zk_config};
    use p3_baby_bear::BabyBear as P3BabyBear;
    use p3_uni_stark::{prove, verify};

    /// A hiding (zero-knowledge) proof of a `DslCircuit`, produced through the
    /// `HidingFriPcs` uni-STARK config. Same proof type the rest of the ZK path
    /// uses (`crate::stark_zk::DreggZkProof`).
    pub type DslZkProof = DreggZkProof;

    /// Prove a `DslCircuit` with **zero knowledge**: the resulting proof is
    /// statistically hiding (trace doubling + random FRI codeword + salted
    /// Merkle leaves), so its openings reveal nothing about the witness beyond
    /// the public inputs. The constraints enforced are exactly those of the
    /// audited [`prove_dsl_p3`](super::prove_dsl_p3) path (same `DslP3Air`, same
    /// hash-aux extension).
    ///
    /// `trace` is the base-width witness (descriptor `trace_width`); the hash
    /// constraints' Poseidon2 aux blocks are appended internally exactly as the
    /// non-hiding path does.
    pub fn prove_dsl_zk(
        dsl: &DslCircuit,
        trace: &[Vec<BabyBear>],
        public_inputs: &[BabyBear],
    ) -> Result<DslZkProof, DslP3Error> {
        let air = DslP3Air::try_from_dsl(dsl)?;
        let full_trace = extend_trace_with_hash_aux(dsl, trace);
        let matrix = to_matrix(&full_trace);
        let pis: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();
        let config = create_zk_config();
        let proof = prove(&config, &air, matrix, &pis);
        // Self-verify (a returned proof is one the hiding verifier accepts).
        verify(&config, &air, &proof, &pis).map_err(|e| DslP3Error::VerificationFailed {
            reason: format!("{e:?}"),
        })?;
        Ok(proof)
    }

    /// Verify a hiding `DslCircuit` proof produced by [`prove_dsl_zk`]. Witness-
    /// free: reconstructs the `DslP3Air` from the descriptor and checks the
    /// proof against the public inputs through the hiding uni-STARK verifier.
    pub fn verify_dsl_zk(
        dsl: &DslCircuit,
        proof: &DslZkProof,
        public_inputs: &[BabyBear],
    ) -> Result<(), DslP3Error> {
        let air = DslP3Air::try_from_dsl(dsl)?;
        let pis: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();
        let config = create_zk_config();
        verify(&config, &air, proof, &pis).map_err(|e| DslP3Error::VerificationFailed {
            reason: format!("{e:?}"),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dsl::circuit::{
        BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr,
        PolyTerm,
    };

    /// A minimal algebraic Transfer-shape descriptor: width-2 trace
    /// `[balance, delta_is_out]`, public input `[final_balance]`. Constraint:
    /// `balance` on the last row equals the published `final_balance`. This is
    /// the anti-ghost commit tooth in miniature: the post-state value is bound
    /// to a public input through the AUDITED verifier.
    fn transfer_shape_descriptor() -> CircuitDescriptor {
        CircuitDescriptor {
            name: "dsl_p3_transfer_shape".to_string(),
            trace_width: 2,
            max_degree: 2,
            columns: vec![
                ColumnDef {
                    name: "balance".into(),
                    index: 0,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "dir".into(),
                    index: 1,
                    kind: ColumnKind::Binary,
                },
            ],
            constraints: vec![
                // direction is boolean
                ConstraintExpr::Binary { col: 1 },
            ],
            boundaries: vec![
                // last row balance == public_input[0]  (the post-state tooth)
                BoundaryDef::PiBinding {
                    row: BoundaryRow::Last,
                    col: 0,
                    pi_index: 0,
                },
            ],
            public_input_count: 1,
            lookup_tables: vec![],
        }
    }

    #[test]
    fn algebraic_descriptor_proves_and_verifies_through_audited_p3() {
        let dsl = DslCircuit::new(transfer_shape_descriptor());
        // 4-row trace; balance settles to 700; direction boolean each row.
        let trace = vec![
            vec![BabyBear::new(1000), BabyBear::new(1)],
            vec![BabyBear::new(900), BabyBear::new(1)],
            vec![BabyBear::new(800), BabyBear::new(0)],
            vec![BabyBear::new(700), BabyBear::new(1)],
        ];
        let pis = vec![BabyBear::new(700)];

        let proof = prove_dsl_p3(&dsl, &trace, &pis)
            .expect("honest algebraic descriptor must prove+verify through audited p3");
        verify_dsl_p3(&dsl, &proof, &pis).expect("audited p3 verify must accept the honest proof");
    }

    /// THE ANTI-GHOST TOOTH on the audited verifier: a forged post-state
    /// (claim final_balance = 999 when the trace ends at 700) must be REJECTED
    /// by the real Plonky3 verifier, exactly as the bespoke verifier rejected
    /// PI tampering.
    #[test]
    fn forged_post_state_rejected_by_audited_p3() {
        let dsl = DslCircuit::new(transfer_shape_descriptor());
        let trace = vec![
            vec![BabyBear::new(1000), BabyBear::new(1)],
            vec![BabyBear::new(900), BabyBear::new(1)],
            vec![BabyBear::new(800), BabyBear::new(0)],
            vec![BabyBear::new(700), BabyBear::new(1)],
        ];
        let honest_pis = vec![BabyBear::new(700)];
        let proof = prove_dsl_p3(&dsl, &trace, &honest_pis).expect("honest proof");

        // Forge the public post-state: claim 999.
        let forged_pis = vec![BabyBear::new(999)];
        let res = verify_dsl_p3(&dsl, &proof, &forged_pis);
        assert!(
            res.is_err(),
            "forged post-state (999 != 700) MUST be rejected by the audited p3 verifier"
        );
    }

    /// A Polynomial-form algebraic constraint also round-trips: enforce
    /// `2*c0 - c1 == 0` (i.e. c1 = 2*c0) on every row via a Polynomial term.
    #[test]
    fn polynomial_constraint_round_trips_through_p3() {
        let desc = CircuitDescriptor {
            name: "dsl_p3_poly".to_string(),
            trace_width: 2,
            max_degree: 1,
            columns: vec![
                ColumnDef {
                    name: "x".into(),
                    index: 0,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "y".into(),
                    index: 1,
                    kind: ColumnKind::Value,
                },
            ],
            constraints: vec![ConstraintExpr::Polynomial {
                // 2*c0 + (-1)*c1 == 0  →  c1 = 2*c0. (-1) mod p = BABYBEAR_P - 1.
                terms: vec![
                    PolyTerm {
                        coeff: BabyBear::new(2),
                        col_indices: vec![0],
                    },
                    PolyTerm {
                        coeff: BabyBear::new(crate::field::BABYBEAR_P - 1),
                        col_indices: vec![1],
                    },
                ],
            }],
            boundaries: vec![],
            public_input_count: 0,
            lookup_tables: vec![],
        };
        let dsl = DslCircuit::new(desc);
        let trace = vec![
            vec![BabyBear::new(3), BabyBear::new(6)],
            vec![BabyBear::new(5), BabyBear::new(10)],
            vec![BabyBear::new(7), BabyBear::new(14)],
            vec![BabyBear::new(9), BabyBear::new(18)],
        ];
        let proof = prove_dsl_p3(&dsl, &trace, &[]).expect("poly proof");
        verify_dsl_p3(&dsl, &proof, &[]).expect("poly verify");

        // Tamper a row so y != 2x: the audited verifier must reject (we forge by
        // proving a bad trace — prove_dsl_p3 self-verifies, so it should error).
        let bad_trace = vec![
            vec![BabyBear::new(3), BabyBear::new(6)],
            vec![BabyBear::new(5), BabyBear::new(99)], // 99 != 10
            vec![BabyBear::new(7), BabyBear::new(14)],
            vec![BabyBear::new(9), BabyBear::new(18)],
        ];
        let res = prove_dsl_p3(&dsl, &bad_trace, &[]);
        assert!(
            res.is_err(),
            "trace violating y=2x must not produce a verifying p3 proof"
        );
    }

    /// REAL Poseidon2 in-circuit hashing through the audited p3 verifier: a
    /// `Hash2to1` constraint (`out == Poseidon2(a,b)`) proves+verifies, and a
    /// forged digest is REJECTED by the genuine permutation constraints.
    #[test]
    fn hash2to1_real_poseidon2_round_trips_through_p3() {
        use crate::poseidon2::hash_2_to_1;

        let desc = CircuitDescriptor {
            name: "dsl_p3_hash2to1".to_string(),
            trace_width: 3, // [a, b, out]
            max_degree: 7,  // Poseidon2 S-box
            columns: vec![
                ColumnDef {
                    name: "a".into(),
                    index: 0,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "b".into(),
                    index: 1,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "out".into(),
                    index: 2,
                    kind: ColumnKind::Hash,
                },
            ],
            constraints: vec![ConstraintExpr::Hash2to1 {
                output_col: 2,
                input_col_a: 0,
                input_col_b: 1,
            }],
            boundaries: vec![],
            public_input_count: 0,
            lookup_tables: vec![],
        };
        let dsl = DslCircuit::new(desc);

        let a = BabyBear::new(111);
        let b = BabyBear::new(222);
        let out = hash_2_to_1(a, b);
        // 4 rows (power-of-two), all the same honest hash.
        let trace = vec![vec![a, b, out]; 4];
        let proof = prove_dsl_p3(&dsl, &trace, &[])
            .expect("honest Poseidon2 hash must prove+verify through audited p3");
        verify_dsl_p3(&dsl, &proof, &[]).expect("audited p3 verify accepts the honest hash");

        // Forge the digest: claim a wrong `out`. The in-circuit permutation
        // constraints must make this UNSAT (prove self-verifies → error).
        let forged = vec![vec![a, b, out + BabyBear::new(1)]; 4];
        let res = prove_dsl_p3(&dsl, &forged, &[]);
        assert!(
            res.is_err(),
            "a forged Poseidon2 digest MUST be rejected by the in-circuit permutation constraints"
        );
    }

    /// REAL Poseidon2 `hash_fact` SPONGE in-circuit through the audited p3
    /// verifier: a `Hash` constraint (`out == hash_fact(predicate, terms)`)
    /// proves+verifies, and a forged digest is REJECTED by the genuine
    /// permutation constraints. This is the form the derivation `derived_hash`
    /// and the non-revocation node-hashes use, so it is the load-bearing
    /// arithmetization that retires those legs' bespoke `stark` path.
    #[test]
    fn hash_sponge_real_poseidon2_round_trips_through_p3() {
        use crate::poseidon2::hash_fact;

        // predicate + 3 terms (cols 0..4), digest at col 4.
        let desc = CircuitDescriptor {
            name: "dsl_p3_hash_sponge".to_string(),
            trace_width: 5, // [pred, t0, t1, t2, out]
            max_degree: 7,  // Poseidon2 S-box
            columns: vec![
                ColumnDef {
                    name: "pred".into(),
                    index: 0,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "t0".into(),
                    index: 1,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "t1".into(),
                    index: 2,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "t2".into(),
                    index: 3,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "out".into(),
                    index: 4,
                    kind: ColumnKind::Hash,
                },
            ],
            constraints: vec![ConstraintExpr::Hash {
                output_col: 4,
                input_cols: vec![0, 1, 2, 3],
            }],
            boundaries: vec![],
            public_input_count: 0,
            lookup_tables: vec![],
        };
        let dsl = DslCircuit::new(desc);

        let pred = BabyBear::new(7);
        let t0 = BabyBear::new(101);
        let t1 = BabyBear::new(202);
        let t2 = BabyBear::new(303);
        let out = hash_fact(pred, &[t0, t1, t2]);
        let trace = vec![vec![pred, t0, t1, t2, out]; 4];

        let proof = prove_dsl_p3(&dsl, &trace, &[])
            .expect("honest hash_fact sponge must prove+verify through audited p3");
        verify_dsl_p3(&dsl, &proof, &[]).expect("audited p3 verify accepts the honest sponge hash");

        // ANTI-GHOST: forge the digest. The in-circuit permutation constraints
        // must make this UNSAT (prove self-verifies → error).
        let forged = vec![vec![pred, t0, t1, t2, out + BabyBear::new(1)]; 4];
        let res = prove_dsl_p3(&dsl, &forged, &[]);
        assert!(
            res.is_err(),
            "a forged hash_fact sponge digest MUST be rejected by the in-circuit Poseidon2"
        );
    }

    /// Interior-row boundary (`Index(k)`, k>0) through the AUDITED p3 verifier
    /// via the sound row-indicator gadget: bind `col 0` at row 2 to public
    /// input 0. An honest trace (row 2's col 0 == PI) proves+verifies, and a
    /// forgery (row 2's col 0 != PI) is REJECTED — the IsZero gadget fires on
    /// exactly row 2 because the counter pins `row_idx`.
    #[test]
    fn interior_row_boundary_round_trips_and_rejects_forgery() {
        let desc = CircuitDescriptor {
            name: "dsl_p3_interior_row".to_string(),
            trace_width: 1, // [v]
            max_degree: 2,
            columns: vec![ColumnDef {
                name: "v".into(),
                index: 0,
                kind: ColumnKind::Value,
            }],
            constraints: vec![],
            boundaries: vec![BoundaryDef::PiBinding {
                row: BoundaryRow::Index(2), // INTERIOR row
                col: 0,
                pi_index: 0,
            }],
            public_input_count: 1,
            lookup_tables: vec![],
        };
        let dsl = DslCircuit::new(desc);

        // 4-row trace; row 2 carries the bound value 777.
        let trace = vec![
            vec![BabyBear::new(10)],
            vec![BabyBear::new(20)],
            vec![BabyBear::new(777)], // row 2 == PI[0]
            vec![BabyBear::new(40)],
        ];
        let pis = vec![BabyBear::new(777)];
        let proof = prove_dsl_p3(&dsl, &trace, &pis)
            .expect("honest interior-row binding must prove+verify through audited p3");
        verify_dsl_p3(&dsl, &proof, &pis)
            .expect("audited p3 verify accepts honest interior binding");

        // ANTI-GHOST: a forged PI[0] (claim row 2 == 999) must be rejected.
        let forged_pis = vec![BabyBear::new(999)];
        let res = verify_dsl_p3(&dsl, &proof, &forged_pis);
        assert!(
            res.is_err(),
            "SOUNDNESS: an interior-row binding to the wrong value MUST be rejected"
        );

        // ANTI-GHOST: a trace where row 2 != PI cannot produce a verifying proof
        // (prove self-verifies → error). The counter pins which row is checked.
        let bad_trace = vec![
            vec![BabyBear::new(10)],
            vec![BabyBear::new(20)],
            vec![BabyBear::new(778)], // row 2 != 777
            vec![BabyBear::new(40)],
        ];
        let res = prove_dsl_p3(&dsl, &bad_trace, &pis);
        assert!(
            res.is_err(),
            "SOUNDNESS: a trace violating the interior-row binding must not verify"
        );
    }

    /// `MerkleHash` (position-indexed) is not handled here — it routes to
    /// the Lean-emitted IR2 membership descriptor. Confirm it is surfaced, not silently dropped.
    #[test]
    fn merklehash_surfaced_not_silently_dropped() {
        let desc = CircuitDescriptor {
            name: "dsl_p3_merkle".to_string(),
            trace_width: 6,
            max_degree: 7,
            columns: vec![],
            constraints: vec![ConstraintExpr::MerkleHash {
                output_col: 5,
                current_col: 0,
                sib_cols: [1, 2, 3],
                position_col: 4,
            }],
            boundaries: vec![],
            public_input_count: 0,
            lookup_tables: vec![],
        };
        let dsl = DslCircuit::new(desc);
        match DslP3Air::try_from_dsl(&dsl) {
            Err(DslP3Error::NonAlgebraicConstraint { .. }) => {}
            other => panic!("expected MerkleHash to be surfaced, got {other:?}"),
        }
    }
}
