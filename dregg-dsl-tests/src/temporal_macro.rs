//! Temporal predicate defined using the `#[dregg_circuit]` macro.
//!
//! Macro-based equivalent of `temporal_dsl.rs` v2 with state_root and 4 PIs.

use dregg_circuit::field::BabyBear;
use dregg_dsl::dregg_circuit;

pub const VALUE: usize = 0;
pub const THRESHOLD: usize = 1;
pub const DIFF: usize = 2;
pub const DIFF_BITS_START: usize = 3;
pub const NUM_DIFF_BITS: usize = 30;
pub const ACCUMULATOR: usize = DIFF_BITS_START + NUM_DIFF_BITS;
pub const STEP_INDEX: usize = ACCUMULATOR + 1;
pub const STATE_ROOT: usize = STEP_INDEX + 1;
pub const ACC_PLUS_ONE: usize = STATE_ROOT + 1;
pub const STEP_PLUS_ONE: usize = ACC_PLUS_ONE + 1;
pub const DIFF_INV: usize = STEP_PLUS_ONE + 1;
pub const NEQ_SELECTOR: usize = DIFF_INV + 1;
pub const TRACE_WIDTH: usize = NEQ_SELECTOR + 1;

pub const PI_THRESHOLD: usize = 0;
pub const PI_NUM_STEPS: usize = 1;
pub const PI_INITIAL_STATE_ROOT: usize = 2;
pub const PI_FINAL_STATE_ROOT: usize = 3;
pub const PUBLIC_INPUT_COUNT: usize = 4;

#[dregg_circuit]
mod temporal_predicate {
    const WIDTH: usize = 40;
    const DEGREE: usize = 2;
    const PI_COUNT: usize = 4;

    mod col {
        pub const VALUE: usize = 0;
        pub const THRESHOLD: usize = 1;
        pub const DIFF: usize = 2;
        pub const DIFF_BITS_START: usize = 3;
        pub const NUM_DIFF_BITS: usize = 30;
        pub const ACCUMULATOR: usize = 33;
        pub const STEP_INDEX: usize = 34;
        pub const STATE_ROOT: usize = 35;
        pub const ACC_PLUS_ONE: usize = 36;
        pub const STEP_PLUS_ONE: usize = 37;
        pub const NEQ_SELECTOR: usize = 39;
    }

    fn constraints(
        local: &[dregg_circuit::field::BabyBear],
        _next: &[dregg_circuit::field::BabyBear],
        pi: &[dregg_circuit::field::BabyBear],
    ) -> Vec<dregg_circuit::field::BabyBear> {
        use dregg_circuit::field::BabyBear;
        let mut cs = Vec::new();
        cs.push(local[col::DIFF] - (local[col::VALUE] - local[col::THRESHOLD]));
        for i in 0..col::NUM_DIFF_BITS {
            let bit = local[col::DIFF_BITS_START + i];
            cs.push(bit * (bit - BabyBear::ONE));
        }
        {
            let mut rec = BabyBear::ZERO;
            let mut p2 = BabyBear::ONE;
            let two = BabyBear::new(2);
            for i in 0..col::NUM_DIFF_BITS {
                rec = rec + local[col::DIFF_BITS_START + i] * p2;
                p2 = p2 * two;
            }
            cs.push(rec - local[col::DIFF]);
        }
        cs.push(local[col::DIFF_BITS_START + col::NUM_DIFF_BITS - 1]);
        cs.push(local[col::ACC_PLUS_ONE] - local[col::ACCUMULATOR] - BabyBear::ONE);
        cs.push(local[col::STEP_PLUS_ONE] - local[col::STEP_INDEX] - BabyBear::ONE);
        cs.push(local[col::THRESHOLD] - pi[0]);
        let ns = local[col::NEQ_SELECTOR];
        cs.push(ns * (ns - BabyBear::ONE));
        cs
    }

    fn transitions(
        local: &[dregg_circuit::field::BabyBear],
        next: &[dregg_circuit::field::BabyBear],
    ) -> Vec<dregg_circuit::field::BabyBear> {
        vec![
            next[col::ACCUMULATOR] - local[col::ACC_PLUS_ONE],
            next[col::STEP_INDEX] - local[col::STEP_PLUS_ONE],
        ]
    }

    fn boundaries(
        pi: &[dregg_circuit::field::BabyBear],
        trace_len: usize,
    ) -> Vec<(usize, usize, dregg_circuit::field::BabyBear)> {
        use dregg_circuit::field::BabyBear;
        vec![
            (0, col::ACCUMULATOR, BabyBear::ONE),
            (0, col::STEP_INDEX, BabyBear::ZERO),
            (0, col::STATE_ROOT, pi[2]),
            (trace_len - 1, col::ACCUMULATOR, pi[1]),
            (trace_len - 1, col::STATE_ROOT, pi[3]),
        ]
    }
}

pub fn generate_temporal_trace(
    values: &[u32],
    state_roots: &[BabyBear],
    threshold: u32,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let n = values.len();
    assert!(n >= 1);
    assert_eq!(n, state_roots.len());
    let padded = n.next_power_of_two().max(2);
    let mut trace = Vec::with_capacity(padded);
    for step in 0..padded {
        let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];
        let val = if step < n {
            values[step]
        } else {
            values[n - 1]
        };
        let sr = if step < n {
            state_roots[step]
        } else {
            *state_roots.last().unwrap()
        };
        let vf = BabyBear::new(val);
        let tf = BabyBear::new(threshold);
        row[VALUE] = vf;
        row[THRESHOLD] = tf;
        row[STATE_ROOT] = sr;
        let diff = vf - tf;
        row[DIFF] = diff;
        let dv = diff.as_u32();
        for i in 0..NUM_DIFF_BITS {
            row[DIFF_BITS_START + i] = BabyBear::new((dv >> i) & 1);
        }
        let acc = (step + 1) as u32;
        row[ACCUMULATOR] = BabyBear::new(acc);
        row[STEP_INDEX] = BabyBear::new(step as u32);
        row[ACC_PLUS_ONE] = BabyBear::new(acc + 1);
        row[STEP_PLUS_ONE] = BabyBear::new(step as u32 + 1);
        trace.push(row);
    }
    let pi = vec![
        BabyBear::new(threshold),
        BabyBear::new(padded as u32),
        state_roots[0],
        *state_roots.last().unwrap(),
    ];
    (trace, pi)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit::stark::{self, StarkAir};

    fn test_state_roots(n: usize) -> Vec<BabyBear> {
        (0..n).map(|i| BabyBear::new(1000 + i as u32)).collect()
    }

    #[test]
    fn test_macro_circuit_struct_exists() {
        let c = TemporalPredicate;
        assert_eq!(c.width(), 40);
        assert_eq!(c.constraint_degree(), 2);
        assert_eq!(c.air_name(), "dregg-temporal_predicate-v1");
    }

    #[test]
    fn test_macro_circuit_valid_trace() {
        let c = TemporalPredicate;
        let sr = test_state_roots(3);
        let (trace, pi) = generate_temporal_trace(&[100, 100, 100], &sr, 50);
        assert_eq!(trace.len(), 4);
        let alpha = BabyBear::new(7);
        for i in 0..trace.len() - 1 {
            assert_eq!(
                c.eval_constraints(&trace[i], &trace[i + 1], &pi, alpha),
                BabyBear::ZERO,
                "row {i}"
            );
        }
    }

    #[test]
    fn test_macro_circuit_boundaries() {
        let c = TemporalPredicate;
        let sr = test_state_roots(3);
        let (trace, pi) = generate_temporal_trace(&[100, 100, 100], &sr, 50);
        let b = c.boundary_constraints(&pi, trace.len());
        assert_eq!(b.len(), 5);
        assert_eq!(b[0].value, BabyBear::ONE);
        assert_eq!(b[2].col, STATE_ROOT);
        assert_eq!(b[2].value, sr[0]);
        assert_eq!(b[4].col, STATE_ROOT);
        assert_eq!(b[4].value, sr[2]);
    }

    #[test]
    fn test_macro_circuit_invalid_value_below_threshold() {
        let c = TemporalPredicate;
        let sr = test_state_roots(3);
        let (trace, pi) = generate_temporal_trace(&[100, 30, 100], &sr, 50);
        assert_ne!(
            c.eval_constraints(&trace[1], &trace[2], &pi, BabyBear::new(7)),
            BabyBear::ZERO
        );
    }

    #[test]
    fn test_macro_circuit_transition_detects_gap() {
        let c = TemporalPredicate;
        let sr = test_state_roots(3);
        let (mut trace, pi) = generate_temporal_trace(&[100, 100, 100], &sr, 50);
        trace[2][ACCUMULATOR] = BabyBear::new(4);
        trace[2][ACC_PLUS_ONE] = BabyBear::new(5);
        assert_ne!(
            c.eval_constraints(&trace[1], &trace[2], &pi, BabyBear::new(7)),
            BabyBear::ZERO
        );
        assert_eq!(
            c.eval_constraints(&trace[0], &trace[1], &pi, BabyBear::new(7)),
            BabyBear::ZERO
        );
    }

    #[test]
    fn test_macro_circuit_full_stark_prove_verify() {
        let c = TemporalPredicate;
        let sr = test_state_roots(3);
        let (trace, pi) = generate_temporal_trace(&[100, 100, 100], &sr, 50);
        let proof = stark::prove(&c, &trace, &pi);
        assert!(stark::verify(&c, &proof, &pi).is_ok());
    }

    #[test]
    fn test_macro_circuit_rejects_wrong_public_inputs() {
        let c = TemporalPredicate;
        let sr = test_state_roots(3);
        let (trace, pi) = generate_temporal_trace(&[100, 100, 100], &sr, 50);
        let proof = stark::prove(&c, &trace, &pi);
        assert!(stark::verify(&c, &proof, &vec![BabyBear::new(99), pi[1], pi[2], pi[3]]).is_err());
    }

    #[test]
    fn test_macro_circuit_rejects_wrong_state_root() {
        let c = TemporalPredicate;
        let sr = test_state_roots(3);
        let (trace, pi) = generate_temporal_trace(&[100, 100, 100], &sr, 50);
        let proof = stark::prove(&c, &trace, &pi);
        assert!(
            stark::verify(&c, &proof, &vec![pi[0], pi[1], BabyBear::new(99999), pi[3]]).is_err()
        );
        assert!(
            stark::verify(&c, &proof, &vec![pi[0], pi[1], pi[2], BabyBear::new(99999)]).is_err()
        );
    }

    #[test]
    fn test_macro_matches_descriptor_constraints() {
        use dregg_dsl_runtime::circuit::DslCircuit;
        let c = TemporalPredicate;
        let dc = DslCircuit::new(super::super::temporal_dsl::temporal_predicate_descriptor(
            super::super::temporal_dsl::TemporalPredicateKind::Gte,
        ));
        let sr = test_state_roots(3);
        let (trace, pi) = generate_temporal_trace(&[100, 100, 100], &sr, 50);
        let alpha = BabyBear::new(13);
        for i in 0..trace.len() - 1 {
            assert_eq!(
                c.eval_constraints(&trace[i], &trace[i + 1], &pi, alpha),
                dc.eval_constraints(&trace[i], &trace[i + 1], &pi, alpha),
                "row {i}"
            );
        }
    }
}
