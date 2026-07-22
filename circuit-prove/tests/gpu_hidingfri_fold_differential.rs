use std::marker::PhantomData;
use std::time::Instant;

use dregg_circuit_prove::gpu_hidingfri_fold::{
    GpuTwoAdicFriFolding, HidingFriChallenge, fold_hidingfri_matrix_wgpu_required,
    hidingfri_fold_counters,
};
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_fri::{FriFoldingStrategy, TwoAdicFriFolding};
use p3_matrix::dense::RowMajorMatrix;

fn challenge(seed: u32) -> HidingFriChallenge {
    HidingFriChallenge::new([
        BabyBear::new(seed),
        BabyBear::new(seed.wrapping_mul(17).wrapping_add(3)),
        BabyBear::new(seed.wrapping_mul(257).wrapping_add(5)),
        BabyBear::new(seed.wrapping_mul(65_537).wrapping_add(7)),
    ])
}

fn inputs(len: usize) -> Vec<HidingFriChallenge> {
    (0..len)
        .map(|index| challenge((index as u32).wrapping_mul(1_000_003).wrapping_add(11)))
        .collect()
}

fn cpu_fold(
    beta: HidingFriChallenge,
    log_arity: usize,
    values: Vec<HidingFriChallenge>,
) -> Vec<HidingFriChallenge> {
    let arity = 1 << log_arity;
    <TwoAdicFriFolding<(), core::convert::Infallible> as FriFoldingStrategy<
        BabyBear,
        HidingFriChallenge,
    >>::fold_matrix(
        &TwoAdicFriFolding(PhantomData),
        beta,
        log_arity,
        RowMajorMatrix::new(values, arity),
    )
}

#[test]
#[ignore = "required WGPU differential; run on hbox with --run-ignored all"]
fn deployed_arities_are_bit_exact_against_pinned_plonky3() {
    let before = hidingfri_fold_counters();
    let mut adapter = None;
    for log_arity in 1..=3 {
        for log_input_len in [10usize, 15, 20] {
            let values = inputs(1 << log_input_len);
            let beta = challenge(0x1539_7a4d ^ (log_arity as u32) ^ (log_input_len as u32));

            let cpu_started = Instant::now();
            let expected = cpu_fold(beta, log_arity, values.clone());
            let cpu_elapsed = cpu_started.elapsed();
            let gpu = fold_hidingfri_matrix_wgpu_required(beta, log_arity, &values)
                .expect("strict hbox gate requires a real WGPU fold");
            adapter.get_or_insert_with(|| gpu.adapter_name.clone());
            assert_eq!(
                gpu.output, expected,
                "WGPU FRI fold diverged at log_arity={log_arity}, log_input_len={log_input_len}"
            );
            eprintln!(
                "HidingFRI fold adapter={} log_arity={} input={} output={} GPU={:.6}s CPU={:.6}s",
                gpu.adapter_name,
                log_arity,
                values.len(),
                gpu.output.len(),
                gpu.elapsed.as_secs_f64(),
                cpu_elapsed.as_secs_f64(),
            );
        }
    }
    // This is the exact `FriFoldingStrategy` call shape consumed by
    // `p3_fri::prover::prove_fri`; the upstream patch only makes the currently
    // hard-coded strategy value injectable from `TwoAdicFriPcs::open`.
    let strategy_values = inputs(1 << 15);
    let strategy_beta = challenge(0x6a09_e667);
    let strategy_expected = cpu_fold(strategy_beta, 3, strategy_values.clone());
    let strategy_actual = GpuTwoAdicFriFolding::<(), core::convert::Infallible>::new(true)
        .fold_matrix(strategy_beta, 3, RowMajorMatrix::new(strategy_values, 8));
    assert_eq!(strategy_actual, strategy_expected);

    let after = hidingfri_fold_counters();
    assert_eq!(after.gpu_folds - before.gpu_folds, 10);
    assert!(after.gpu_input_elements > before.gpu_input_elements);
    assert!(after.gpu_output_elements > before.gpu_output_elements);
    assert!(adapter.is_some());
}

#[test]
fn malformed_shapes_refuse_before_dispatch() {
    let beta = HidingFriChallenge::ONE;
    assert!(fold_hidingfri_matrix_wgpu_required(beta, 0, &inputs(8)).is_err());
    assert!(fold_hidingfri_matrix_wgpu_required(beta, 4, &inputs(16)).is_err());
    assert!(fold_hidingfri_matrix_wgpu_required(beta, 3, &inputs(12)).is_err());
}
