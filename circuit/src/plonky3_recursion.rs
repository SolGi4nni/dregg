//! A small Poseidon2 hash-chain aggregation AIR ([`AggregationAir`]).
//!
//! [`AggregationAir`] constrains a width-4 trace as a running accumulator: each
//! row carries `(acc_in, leaf, root, acc_out)`, the first row's `acc_in` equals
//! public input 0, the last row's `acc_out` equals public input 1, and the chain
//! is continuous (`acc_out[i] == acc_in[i+1]`).
//!
//! It is a deliberately minimal, self-contained AIR. The recursion-engine tests
//! in `circuit-prove` borrow it as a generic "some AIR" smoke wrap — e.g. the
//! VK-pin negative test in `circuit-prove/tests/ivc_turn_chain_rotated.rs` and
//! the recursion-shape smoke tests in `plonky3_recursion_impl::tests`.
//!
//! The live whole-chain recursion rides the real `emberian/plonky3-recursion`
//! fork through `circuit-prove/src/ivc_turn_chain.rs` (depth: N turns → one
//! constant-cost recursive STARK) and `circuit/src/joint_turn_recursive.rs`
//! (width: N cells → one batch-STARK).

use p3_air::WindowAccess;
use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::PrimeCharacteristicRing;

// ============================================================================
// Aggregation AIR
// ============================================================================

/// A CONTINUITY-ONLY aggregation scaffold (test/smoke AIR).
///
/// Trace layout (width = 4):
/// - col 0: accumulator_in (chain state before this step)
/// - col 1: leaf_hash (public input from inner proof i)
/// - col 2: root_hash (public input from inner proof i)
/// - col 3: accumulator_out — the prover is EXPECTED to fill this as
///   `hash_4_to_1([acc_in, leaf, root, step_index])`, but `eval` below does NOT
///   constrain it to that hash; it is an unconstrained witness here.
///
/// Public inputs: [initial_accumulator (= 0), final_accumulator]
///
/// Constraints actually enforced (and ONLY these):
/// 1. First row: acc_in = initial_accumulator (public input 0)
/// 2. Last row: acc_out = final_accumulator (public input 1)
/// 3. Chain continuity: acc_out[i] = acc_in[i+1] (on transitions)
///
/// NOTE: this AIR does NOT bind the accumulator to a genuine Poseidon2 fold —
/// cols 1/2 (leaf/root) and the per-row hash are unconstrained, so a satisfying
/// trace proves only endpoint continuity, not history integrity. The deployed,
/// hash-bound whole-chain aggregation rides the `emberian/plonky3-recursion`
/// fork via `circuit-prove`'s `ivc_turn_chain` / `joint_turn_recursive` (whose
/// soundness is `Dregg2.Circuit.{AggAirSound,AggregationAirSound}` in Lean).
/// Keep this as a continuity smoke scaffold; do not treat it as history-binding.
pub struct AggregationAir;

impl<F: PrimeCharacteristicRing + Sync> BaseAir<F> for AggregationAir {
    fn width(&self) -> usize {
        4
    }

    fn num_public_values(&self) -> usize {
        2 // [initial_accumulator, final_accumulator]
    }

    fn main_next_row_columns(&self) -> Vec<usize> {
        // We access next row for chain continuity
        (0..4).collect()
    }
}

impl<AB: AirBuilder> Air<AB> for AggregationAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let next = main.next_slice();

        let acc_in: AB::Expr = local[0].into();
        let acc_out: AB::Expr = local[3].into();
        let next_acc_in: AB::Expr = next[0].into();

        // Copy public values before mutably borrowing builder
        let public_values = builder.public_values();
        let pv0: AB::Expr = public_values[0].into();
        let pv1: AB::Expr = public_values[1].into();

        // Constraint 1: First row accumulator is the initial value (public input 0)
        let first_acc_constraint: AB::Expr = acc_in - pv0;
        builder.when_first_row().assert_zero(first_acc_constraint);

        // Constraint 2: Last row accumulator_out is the final value (public input 1)
        let last_acc_constraint: AB::Expr = acc_out.clone() - pv1;
        builder.when_last_row().assert_zero(last_acc_constraint);

        // Constraint 3: Chain continuity (acc_out[i] = acc_in[i+1])
        let continuity: AB::Expr = acc_out - next_acc_in;
        builder.when_transition().assert_zero(continuity);
    }
}
