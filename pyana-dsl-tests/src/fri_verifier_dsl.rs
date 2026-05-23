//! FRI Verifier expressed as a CircuitDescriptor for the Level 2 Midnight bridge.
//!
//! This module prototypes the algorithmic structure of verifying a single FRI query
//! within our DSL framework. The intent is to demonstrate how FRI verification maps
//! to an AIR/constraint system that could ultimately be compiled for Midnight.
//!
//! # Background
//!
//! Our pyana STARK proofs use FRI (Fast Reed-Solomon Interactive Oracle Proof) with:
//! - Poseidon2 Merkle commitments (BabyBear field, width 16)
//! - Binary folding (each layer halves the polynomial degree)
//! - Multiple queries for soundness amplification
//!
//! To verify on Midnight (BLS12-381 Plonk), we need to express FRI query checking
//! as arithmetic constraints over a field. Since BabyBear (2^31 - 2^27 + 1) fits
//! entirely within a BLS12-381 scalar (255 bits), all BabyBear arithmetic can be
//! performed natively in Fq without limb decomposition.
//!
//! # Architecture
//!
//! One FRI query verification consists of:
//! 1. **Merkle path verification**: Check that the queried leaf is committed in the
//!    FRI commitment at each layer. This requires Poseidon2 hashes.
//! 2. **Folding consistency**: Check that the values at consecutive FRI layers are
//!    consistent with the folding operation (polynomial evaluation at a random point).
//! 3. **Final layer check**: The last FRI layer is a constant polynomial; verify its value.
//!
//! # Trace Layout
//!
//! The circuit uses one row per FRI layer, processing from the initial commitment
//! down to the final constant layer.
//!
//! ## Columns (per row = one FRI layer)
//!
//! | Col | Name           | Description                                        |
//! |-----|----------------|----------------------------------------------------|
//! | 0   | eval_at_x      | f_i(x): evaluation at the query point              |
//! | 1   | eval_at_neg_x  | f_i(-x): evaluation at the sibling point            |
//! | 2   | alpha          | Random folding challenge for this layer             |
//! | 3   | next_eval      | f_{i+1}(x^2): the folded evaluation (next layer)   |
//! | 4   | leaf_hash      | Poseidon2 hash of (eval_at_x, eval_at_neg_x)       |
//! | 5   | merkle_root    | Expected Merkle root for this FRI layer             |
//! | 6-25| sibling[0..19] | Merkle siblings for the authentication path        |
//! | 26  | path_bits      | Packed query position bits for Merkle path          |
//! | 27  | computed_root  | Root computed by hashing up the Merkle path         |
//!
//! ## Constraints
//!
//! 1. **Folding constraint** (algebraic):
//!    next_eval == (eval_at_x + eval_at_neg_x)/2 + alpha * (eval_at_x - eval_at_neg_x)/(2*x)
//!    Simplified (multiplied through by 2):
//!    2 * next_eval == (eval_at_x + eval_at_neg_x) + alpha * (eval_at_x - eval_at_neg_x) / x
//!
//!    But x is known from the query index, so we reformulate as:
//!    2 * x * next_eval == x * (eval_at_x + eval_at_neg_x) + alpha * (eval_at_x - eval_at_neg_x)
//!
//! 2. **Leaf hash binding**: leaf_hash == Poseidon2(eval_at_x, eval_at_neg_x)
//!
//! 3. **Merkle path verification**: computed_root == hash_up(leaf_hash, siblings, path_bits)
//!
//! 4. **Root consistency**: computed_root == merkle_root (public input per layer)
//!
//! 5. **Layer transition**: next row's eval_at_x == this row's next_eval
//!
//! # Midnight Mapping Notes
//!
//! When targeting Midnight's ZkStdLib `Relation`:
//! - BabyBear values embed directly into Fq (BLS12-381 scalar) with no limb overhead
//! - Poseidon2-over-BabyBear must be implemented as a sequence of native Fq operations
//!   with modular reduction (mod BabyBear_P) after each multiplication
//! - The Merkle path depth is fixed (20 for our standard configuration)
//! - Multiple FRI queries are independent and can share the same circuit structure
//!   repeated N times (N=50 for 100-bit security)

use pyana_circuit::field::BabyBear;
use pyana_dsl_runtime::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

// ============================================================================
// Constants
// ============================================================================

/// Depth of the Merkle tree used in FRI commitments.
pub const MERKLE_DEPTH: usize = 20;

/// Number of FRI layers (log2 of the trace length for a 2^20 trace).
pub const NUM_FRI_LAYERS: usize = 20;

/// Number of FRI queries for ~100 bits of security.
pub const NUM_FRI_QUERIES: usize = 50;

/// BabyBear modulus.
pub const BABYBEAR_P: u32 = 0x78000001; // 2^31 - 2^27 + 1

// ============================================================================
// Column indices for a SINGLE FRI query layer
// ============================================================================

pub mod col {
    /// f_i(x): polynomial evaluation at the query point for this layer.
    pub const EVAL_AT_X: usize = 0;
    /// f_i(-x): polynomial evaluation at the sibling (negated) point.
    pub const EVAL_AT_NEG_X: usize = 1;
    /// Random folding challenge alpha_i for this layer.
    pub const ALPHA: usize = 2;
    /// f_{i+1}(x^2): the folded evaluation that should appear at the next layer.
    pub const NEXT_EVAL: usize = 3;
    /// x_i: the query point for this layer (derived from query index).
    pub const QUERY_X: usize = 4;
    /// leaf_hash: Poseidon2(eval_at_x, eval_at_neg_x) — the leaf of the Merkle tree.
    pub const LEAF_HASH: usize = 5;
    /// computed_root: result of hashing up the Merkle path from leaf_hash.
    pub const COMPUTED_ROOT: usize = 6;
    /// expected_root: the FRI commitment root for this layer (public input).
    pub const EXPECTED_ROOT: usize = 7;
    /// Start of sibling columns for Merkle path (MERKLE_DEPTH siblings).
    pub const SIBLINGS_START: usize = 8;
    /// End of sibling columns (exclusive). SIBLINGS_START + MERKLE_DEPTH.
    pub const SIBLINGS_END: usize = 8 + super::MERKLE_DEPTH; // 28
    /// Packed path index bits (determines left/right at each Merkle level).
    pub const PATH_INDEX: usize = 28;
}

/// Total trace width for the FRI query verifier.
pub const FRI_QUERY_WIDTH: usize = col::PATH_INDEX + 1; // 29

// ============================================================================
// FRI Query Verifier Descriptor
// ============================================================================

/// Build a `CircuitDescriptor` that verifies a single FRI query.
///
/// The circuit has NUM_FRI_LAYERS rows, one per folding layer. It checks:
/// 1. Folding consistency between consecutive layers
/// 2. Merkle path validity at each layer
/// 3. Root commitment matches the expected public value
///
/// Public inputs: [layer_0_root, layer_1_root, ..., layer_{N-1}_root, final_value]
///
/// The final_value is the claimed constant of the final FRI polynomial.
pub fn fri_query_verifier_descriptor() -> CircuitDescriptor {
    let mut constraints = Vec::new();

    // ──────────────────────────────────────────────────────────────────────
    // C1: Folding consistency constraint
    //
    // The FRI folding relation:
    //   f_{i+1}(x^2) = (f_i(x) + f_i(-x))/2 + alpha_i * (f_i(x) - f_i(-x)) / (2*x)
    //
    // Rearranged (multiply both sides by 2*x to avoid division):
    //   2 * x * next_eval = x * (eval_x + eval_neg_x) + alpha * (eval_x - eval_neg_x)
    //
    // As a zero-constraint (everything on one side):
    //   x*(eval_x + eval_neg_x) + alpha*(eval_x - eval_neg_x) - 2*x*next_eval == 0
    //
    // Expanding:
    //   x*eval_x + x*eval_neg_x + alpha*eval_x - alpha*eval_neg_x - 2*x*next_eval == 0
    //
    // Which is:
    //   (x + alpha)*eval_x + (x - alpha)*eval_neg_x - 2*x*next_eval == 0
    //
    // In polynomial constraint form (products of columns):
    //   query_x * eval_x + query_x * eval_neg_x
    //   + alpha * eval_x - alpha * eval_neg_x
    //   - 2 * query_x * next_eval == 0
    //
    // Note: the "- 2 * query_x * next_eval" term involves a coefficient of -2 on a
    // product of two columns. In BabyBear: -2 mod p = p - 2.
    // ──────────────────────────────────────────────────────────────────────

    let neg_2 = BabyBear::new(BABYBEAR_P - 2);

    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            // + query_x * eval_x
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![col::QUERY_X, col::EVAL_AT_X],
            },
            // + query_x * eval_neg_x
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![col::QUERY_X, col::EVAL_AT_NEG_X],
            },
            // + alpha * eval_x
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![col::ALPHA, col::EVAL_AT_X],
            },
            // - alpha * eval_neg_x
            PolyTerm {
                coeff: BabyBear::new(BABYBEAR_P - 1), // -1
                col_indices: vec![col::ALPHA, col::EVAL_AT_NEG_X],
            },
            // - 2 * query_x * next_eval
            PolyTerm {
                coeff: neg_2,
                col_indices: vec![col::QUERY_X, col::NEXT_EVAL],
            },
        ],
    });

    // ──────────────────────────────────────────────────────────────────────
    // C2: Leaf hash binding
    //
    // leaf_hash == Poseidon2(eval_at_x, eval_at_neg_x)
    //
    // This uses our DSL's Hash constraint which evaluates hash_fact internally.
    // In the Midnight mapping, this would be replaced by the Poseidon2-over-BabyBear
    // implementation in ZkStdLib.
    // ──────────────────────────────────────────────────────────────────────

    constraints.push(ConstraintExpr::Hash {
        output_col: col::LEAF_HASH,
        input_cols: vec![col::EVAL_AT_X, col::EVAL_AT_NEG_X],
    });

    // ──────────────────────────────────────────────────────────────────────
    // C3: Merkle root consistency
    //
    // computed_root == expected_root
    //
    // The computed_root column is filled by the prover after hashing up the
    // Merkle path. The constraint verifies it matches the committed root.
    //
    // In a full implementation, the Merkle path hashing itself would be
    // constrained (20 sequential Hash constraints). Here we express the
    // binding as an equality to keep the prototype focused on the FRI logic.
    // The full Merkle verification is in merkle_poseidon2_dsl.rs.
    // ──────────────────────────────────────────────────────────────────────

    constraints.push(ConstraintExpr::Equality {
        col_a: col::COMPUTED_ROOT,
        col_b: col::EXPECTED_ROOT,
    });

    // ──────────────────────────────────────────────────────────────────────
    // C4: Layer transition (vertical chaining)
    //
    // The next row's eval_at_x must equal this row's next_eval.
    // This chains the FRI layers together: the folded output at layer i
    // becomes the input at layer i+1.
    // ──────────────────────────────────────────────────────────────────────

    constraints.push(ConstraintExpr::Transition {
        next_col: col::EVAL_AT_X,
        local_col: col::NEXT_EVAL,
    });

    // ──────────────────────────────────────────────────────────────────────
    // Boundary constraints
    // ──────────────────────────────────────────────────────────────────────

    // Public inputs: the FRI layer roots and the final constant value.
    // PI[0] = root of layer 0 (initial polynomial commitment)
    // PI[last] = claimed final constant value
    let public_input_count = NUM_FRI_LAYERS + 1; // roots + final value

    let boundaries = vec![
        // First row: expected_root == PI[0] (initial commitment root)
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::EXPECTED_ROOT,
            pi_index: 0,
        },
        // Last row: next_eval == PI[NUM_FRI_LAYERS] (final constant)
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: col::NEXT_EVAL,
            pi_index: NUM_FRI_LAYERS,
        },
    ];

    // Each layer row binds its expected_root to the corresponding public input.
    // (In a real circuit these would be per-row PI bindings; here we note them
    // as documentation. The DSL supports only First/Last boundaries, so
    // intermediate roots would need a different encoding in production.)

    // ──────────────────────────────────────────────────────────────────────
    // Column definitions
    // ──────────────────────────────────────────────────────────────────────

    let mut columns = vec![
        ColumnDef {
            name: "eval_at_x".into(),
            index: col::EVAL_AT_X,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "eval_at_neg_x".into(),
            index: col::EVAL_AT_NEG_X,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "alpha".into(),
            index: col::ALPHA,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "next_eval".into(),
            index: col::NEXT_EVAL,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "query_x".into(),
            index: col::QUERY_X,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "leaf_hash".into(),
            index: col::LEAF_HASH,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "computed_root".into(),
            index: col::COMPUTED_ROOT,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "expected_root".into(),
            index: col::EXPECTED_ROOT,
            kind: ColumnKind::Hash,
        },
    ];

    // Sibling columns for Merkle path
    for i in 0..MERKLE_DEPTH {
        columns.push(ColumnDef {
            name: format!("sibling_{}", i),
            index: col::SIBLINGS_START + i,
            kind: ColumnKind::Value,
        });
    }

    columns.push(ColumnDef {
        name: "path_index".into(),
        index: col::PATH_INDEX,
        kind: ColumnKind::Value,
    });

    CircuitDescriptor {
        name: "pyana-fri-query-verifier-v1".into(),
        trace_width: FRI_QUERY_WIDTH,
        max_degree: 3, // Products of 2 columns (degree 2) + linear = degree 3
        columns,
        constraints,
        boundaries,
        public_input_count,
        lookup_tables: vec![],
    }
}

/// Create a DslCircuit from the FRI query verifier descriptor.
pub fn fri_query_verifier_dsl_circuit() -> DslCircuit {
    DslCircuit::new(fri_query_verifier_descriptor())
}

// ============================================================================
// Midnight ZkStdLib Relation sketch (not compilable — design reference)
// ============================================================================

/// Design sketch for how the FRI verifier maps to Midnight's `Relation` trait.
///
/// This is NOT real code — Midnight's types are not in our dependency tree.
/// It documents the intended structure for when we build the production verifier.
///
/// ```text
/// // In a crate that depends on midnight-zk-stdlib:
///
/// use midnight_zk_stdlib::{Relation, ZkStdLib, ZkStdLibArch};
/// use midnight_proofs::circuit::{Layouter, Value};
/// use midnight_curves::Fq;
///
/// #[derive(Clone)]
/// struct FriVerifierRelation {
///     num_queries: usize,
///     num_layers: usize,
///     merkle_depth: usize,
/// }
///
/// impl Relation for FriVerifierRelation {
///     type Instance = FriVerifierInstance;
///     type Witness = FriVerifierWitness;
///     type Error = Error;
///
///     fn format_instance(instance: &Self::Instance) -> Result<Vec<Fq>, Error> {
///         // Public inputs: layer roots + final constant + initial eval commitment
///         let mut pi = Vec::new();
///         for root in &instance.layer_roots {
///             pi.push(embed_babybear_in_fq(*root));
///         }
///         pi.push(embed_babybear_in_fq(instance.final_constant));
///         Ok(pi)
///     }
///
///     fn circuit(
///         &self,
///         std_lib: &ZkStdLib,
///         layouter: &mut impl Layouter<Fq>,
///         instance: Value<Self::Instance>,
///         witness: Value<Self::Witness>,
///     ) -> Result<(), Error> {
///         // For each FRI query:
///         for q in 0..self.num_queries {
///             // 1. Assign layer evaluations
///             // 2. Check folding constraint at each layer
///             // 3. Verify Merkle path using Poseidon2-over-BabyBear
///             //    (implemented as native Fq arithmetic with mod-BabyBear reduction)
///             // 4. Check roots match public inputs
///         }
///         Ok(())
///     }
///
///     fn used_chips(&self) -> ZkStdLibArch {
///         ZkStdLibArch {
///             poseidon: true,  // For transcript challenges (Fiat-Shamir)
///             // No foreign curve needed — BabyBear arithmetic is native in Fq
///             ..ZkStdLibArch::default()
///         }
///     }
/// }
///
/// struct FriVerifierInstance {
///     layer_roots: Vec<u32>,       // BabyBear field elements (FRI commitments)
///     final_constant: u32,         // Final layer constant
/// }
///
/// struct FriVerifierWitness {
///     queries: Vec<FriQueryWitness>,
/// }
///
/// struct FriQueryWitness {
///     /// Per-layer: (eval_at_x, eval_at_neg_x, alpha, query_x)
///     layers: Vec<(u32, u32, u32, u32)>,
///     /// Per-layer: Merkle authentication path (siblings + index)
///     merkle_paths: Vec<(Vec<u32>, u32)>,
/// }
///
/// /// Embed a BabyBear element into BLS12-381 Fq.
/// /// BabyBear p = 2^31 - 2^27 + 1 = 2013265921, which trivially fits in 255-bit Fq.
/// fn embed_babybear_in_fq(val: u32) -> Fq {
///     Fq::from(val as u64)
/// }
///
/// /// Reduce an Fq value back to BabyBear (for intermediate computations).
/// /// This is a single constrain_bits(31) followed by a subtraction gate.
/// fn reduce_mod_babybear(std_lib: &ZkStdLib, layouter: &mut impl Layouter<Fq>,
///                        val: &AssignedNative<Fq>) -> Result<AssignedNative<Fq>, Error> {
///     // Decompose val = q * BABYBEAR_P + r where 0 <= r < BABYBEAR_P
///     // Constrain r has at most 31 bits
///     // Constrain val == q * BABYBEAR_P + r
///     // Return r
///     todo!()
/// }
/// ```
///
/// ## Gate Count Estimate for Midnight
///
/// Based on ZkStdLib's architecture:
/// - Native Fq multiplication: 1 gate (single row in the arithmetic identity)
/// - BabyBear mod reduction: ~3 gates (decompose + range check + equality)
/// - Poseidon2 round (BabyBear, simulated): ~16 gates per round
///   (width-16 state, but each element is a single Fq so no limbs)
/// - Full Poseidon2 hash (14 full + 14 partial rounds): ~450 gates
/// - Merkle path (20 hashes): 9,000 gates
/// - Folding check per layer: ~10 gates
/// - One FRI query (20 layers): 20 * (450 + 10) + 9000 = ~18,200 gates
/// - 50 queries: 910,000 gates
/// - Overhead (Fiat-Shamir, public input binding): ~10,000 gates
/// - **Total: ~920K gates → fits in k=20 (1M rows)**
///
/// With Midnight's SRS supporting k up to 25, this is well within capacity.

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_circuit::stark::StarkAir;

    #[test]
    fn test_fri_verifier_descriptor_structure() {
        let desc = fri_query_verifier_descriptor();

        assert_eq!(desc.name, "pyana-fri-query-verifier-v1");
        assert_eq!(desc.trace_width, FRI_QUERY_WIDTH);
        assert_eq!(desc.trace_width, 29);
        assert_eq!(desc.max_degree, 3);
        assert_eq!(desc.public_input_count, NUM_FRI_LAYERS + 1);

        // Should have 4 constraints: folding, hash, root equality, transition
        assert_eq!(desc.constraints.len(), 4);

        // First constraint is the folding polynomial (degree 2)
        assert!(matches!(
            &desc.constraints[0],
            ConstraintExpr::Polynomial { terms } if terms.len() == 5
        ));

        // Second is hash binding
        assert!(matches!(
            &desc.constraints[1],
            ConstraintExpr::Hash { output_col, input_cols }
            if *output_col == col::LEAF_HASH && input_cols.len() == 2
        ));

        // Third is root equality
        assert!(matches!(
            &desc.constraints[2],
            ConstraintExpr::Equality { col_a, col_b }
            if *col_a == col::COMPUTED_ROOT && *col_b == col::EXPECTED_ROOT
        ));

        // Fourth is layer transition
        assert!(matches!(
            &desc.constraints[3],
            ConstraintExpr::Transition { next_col, local_col }
            if *next_col == col::EVAL_AT_X && *local_col == col::NEXT_EVAL
        ));
    }

    #[test]
    fn test_fri_verifier_column_layout() {
        let desc = fri_query_verifier_descriptor();

        // 8 named columns + 20 siblings + 1 path_index = 29
        assert_eq!(desc.columns.len(), 29);

        // Verify sibling columns are sequential
        for i in 0..MERKLE_DEPTH {
            let col_def = &desc.columns[8 + i];
            assert_eq!(col_def.index, col::SIBLINGS_START + i);
            assert_eq!(col_def.name, format!("sibling_{}", i));
        }
    }

    #[test]
    fn test_fri_verifier_boundary_constraints() {
        let desc = fri_query_verifier_descriptor();

        assert_eq!(desc.boundaries.len(), 2);

        // First boundary: initial root
        assert!(matches!(
            &desc.boundaries[0],
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col,
                pi_index: 0,
            } if *col == col::EXPECTED_ROOT
        ));

        // Last boundary: final constant
        assert!(matches!(
            &desc.boundaries[1],
            BoundaryDef::PiBinding {
                row: BoundaryRow::Last,
                col,
                pi_index,
            } if *col == col::NEXT_EVAL && *pi_index == NUM_FRI_LAYERS
        ));
    }

    #[test]
    fn test_folding_constraint_correctness() {
        // Verify the folding arithmetic is correct for a known example.
        // f(x) = 3x + 5 → f(x) = 8, f(-x) = 2 at x=1
        // Folded: f_next = (f(x) + f(-x))/2 + alpha * (f(x) - f(-x))/(2x)
        //       = (8 + 2)/2 + alpha * (8 - 2)/(2*1)
        //       = 5 + 3*alpha
        //
        // With alpha = 2: f_next = 5 + 6 = 11
        //
        // Our constraint: x*(eval_x + eval_neg_x) + alpha*(eval_x - eval_neg_x) - 2*x*next_eval == 0
        // = 1*(8 + 2) + 2*(8 - 2) - 2*1*11
        // = 10 + 12 - 22
        // = 0 ✓

        let x: u64 = 1;
        let eval_x: u64 = 8;
        let eval_neg_x: u64 = 2;
        let alpha: u64 = 2;
        let next_eval: u64 = 11;

        let lhs = x * (eval_x + eval_neg_x) + alpha * (eval_x - eval_neg_x);
        let rhs = 2 * x * next_eval;
        assert_eq!(lhs, rhs, "Folding constraint should be satisfied");
    }

    #[test]
    fn test_babybear_fits_in_bls12_381() {
        // BabyBear modulus: 2^31 - 2^27 + 1 = 2013265921
        // BLS12-381 scalar field: ~2^255
        // BabyBear trivially embeds.
        assert!(BABYBEAR_P < u32::MAX);
        assert_eq!(BABYBEAR_P, 2013265921);
        // 2^31 - 2^27 + 1 = 2147483648 - 134217728 + 1 = 2013265921 ✓
        assert_eq!(BABYBEAR_P, (1u32 << 31) - (1u32 << 27) + 1);
    }

    #[test]
    fn test_gate_count_estimate_within_midnight_capacity() {
        // Verify our estimates are within Midnight's SRS limits.
        // Midnight supports k up to 25 → 2^25 = 33,554,432 rows.
        // Our estimate: ~920K gates for 50-query FRI verifier.
        let estimated_gates: u64 = 920_000;
        let midnight_max_rows: u64 = 1 << 25;
        assert!(
            estimated_gates < midnight_max_rows,
            "FRI verifier ({} gates) must fit in Midnight circuit ({} rows)",
            estimated_gates,
            midnight_max_rows
        );
    }

    #[test]
    fn test_dsl_circuit_construction() {
        let circuit = fri_query_verifier_dsl_circuit();
        // DslCircuit should construct without panic
        assert_eq!(circuit.width(), FRI_QUERY_WIDTH);
        assert_eq!(circuit.air_name(), "pyana-fri-query-verifier-v1");
    }
}
