//! Actual high-level tfhe-rs `FheUint32` weld for the deployed KS->PBS order.

use std::time::Instant;

use fhegg_fhe::tfhe_high_level_wgpu::{
    prepare_fhe_uint32_ks_pbs_transform_wgpu_plan, FheUint32WgpuPbsError,
};
use fhegg_fhe::tfhe_wgpu::{TorusMacBackend, TorusWgpuAlgorithm};
use tfhe::integer::IntegerCiphertext;
use tfhe::prelude::*;
use tfhe::{set_server_key, ClientKey, CompressedServerKey, ConfigBuilder, FheUint32};

#[test]
fn deployed_fhe_uint32_block_lut_matches_tfhe_and_remains_high_level_usable() {
    if std::env::var_os("DREGG_REQUIRE_WGPU").is_none() {
        eprintln!("set DREGG_REQUIRE_WGPU=1 to run the deployed high-level GPU PBS gate");
        return;
    }

    let client = ClientKey::generate(ConfigBuilder::default());
    let compressed = CompressedServerKey::new(&client);
    let server = compressed.decompress();
    let shortint_server: &tfhe::shortint::ServerKey = server.as_ref().as_ref();
    let lookup = shortint_server.generate_lookup_table(|value| (value % 4 + 1) % 4);
    let prepare_started = Instant::now();
    let plan = prepare_fhe_uint32_ks_pbs_transform_wgpu_plan(&compressed).unwrap();
    let prepare_time = prepare_started.elapsed();

    let clear = 0x1234_5678u32;
    let block_index = 3usize;
    let input = FheUint32::encrypt(clear, &client);

    let (mut oracle_radix, oracle_id, oracle_tag, oracle_rerandomization) =
        input.clone().into_raw_parts();
    let oracle_block =
        shortint_server.apply_lookup_table(&oracle_radix.blocks()[block_index], &lookup);
    oracle_radix.blocks_mut()[block_index] = oracle_block;
    let oracle =
        FheUint32::from_raw_parts(oracle_radix, oracle_id, oracle_tag, oracle_rerandomization);

    let gpu_started = Instant::now();
    let (gpu, backend) = plan
        .apply_lookup_table_to_block(&input, block_index, &lookup)
        .unwrap();
    let gpu_time = gpu_started.elapsed();
    assert!(matches!(
        backend,
        TorusMacBackend::Wgpu {
            algorithm: TorusWgpuAlgorithm::ExactTransformResidentPbs,
            ..
        }
    ));
    let oracle_clear: u32 = oracle.decrypt(&client);
    let gpu_clear: u32 = gpu.decrypt(&client);
    assert_eq!(gpu_clear, oracle_clear);
    eprintln!(
        "high-level KS->transform-PBS: prepare={:.3}ms block-LUT={:.3}ms backend={backend:?}",
        prepare_time.as_secs_f64() * 1_000.0,
        gpu_time.as_secs_f64() * 1_000.0,
    );

    // The output is not a private shortint side object: it remains a normal
    // large-key high-level value accepted by the deployed server key.
    set_server_key(server);
    let one = FheUint32::encrypt(1u32, &client);
    let advanced = &gpu + &one;
    let advanced_clear: u32 = advanced.decrypt(&client);
    assert_eq!(advanced_clear, oracle_clear + 1);
}

#[test]
fn deployed_fhe_uint32_scalar_gt_is_all_block_wgpu_and_drives_control_flow() {
    if std::env::var_os("DREGG_REQUIRE_WGPU").is_none() {
        eprintln!("set DREGG_REQUIRE_WGPU=1 to run the deployed scalar comparison GPU gate");
        return;
    }

    let client = ClientKey::generate(ConfigBuilder::default());
    let compressed = CompressedServerKey::new(&client);
    let server = compressed.decompress();
    let prepare_started = Instant::now();
    let plan = prepare_fhe_uint32_ks_pbs_transform_wgpu_plan(&compressed).unwrap();
    let prepare_time = prepare_started.elapsed();
    set_server_key(server);

    // Equal-through-the-last-block, greater-only-at-the-last-block, and an
    // early more-significant less-than decision exercise all three states of
    // the encrypted lexicographic machine. tfhe-rs's independent high-level
    // comparison is the semantic oracle; the WGPU output is decrypted only
    // after both encrypted computations have completed.
    let clear = 0x9234_5678u32;
    let cases = [clear, clear - 1, 0xa234_5678];
    let mut gpu_times = Vec::with_capacity(cases.len());
    let mut true_predicate = None;
    for scalar in cases {
        let input = FheUint32::encrypt(clear, &client);
        let oracle = input.gt(scalar);
        let gpu_started = Instant::now();
        let (gpu, backends) = plan.greater_than_scalar(&input, scalar).unwrap();
        let gpu_time = gpu_started.elapsed();
        gpu_times.push(gpu_time);
        assert_eq!(
            backends.len(),
            16,
            "one WGPU PBS is required per radix block"
        );
        assert!(backends.iter().all(|backend| matches!(
            backend,
            TorusMacBackend::Wgpu {
                algorithm: TorusWgpuAlgorithm::ExactTransformResidentPbs,
                ..
            }
        )));
        let oracle_clear: bool = oracle.decrypt(&client);
        let gpu_clear: u32 = gpu.decrypt(&client);
        assert_eq!(gpu_clear, u32::from(oracle_clear));
        if gpu_clear == 1 {
            true_predicate = Some(gpu);
        }
        eprintln!(
            "high-level scalar-gt: clear={clear:#010x} scalar={scalar:#010x} result={gpu_clear} 16-block-WGPU={:.3}ms",
            gpu_time.as_secs_f64() * 1_000.0,
        );
    }

    // Dark-Bazaar-shaped producer: aggregate legal encrypted quantities first,
    // then compare the settled multi-block sum without exposing the aggregate.
    // This also crosses the old u16 boundary (32768 + 32768 = 65536).
    let encrypted_quantities = [
        FheUint32::encrypt(32_768u32, &client),
        FheUint32::encrypt(32_768u32, &client),
    ];
    let quantity_refs = encrypted_quantities.iter().collect::<Vec<_>>();
    let aggregate = FheUint32::sum(&quantity_refs);
    let aggregate_oracle = aggregate.gt(65_535u32);
    let aggregate_started = Instant::now();
    let (aggregate_gpu, aggregate_backends) = plan.greater_than_scalar(&aggregate, 65_535).unwrap();
    let aggregate_time = aggregate_started.elapsed();
    assert_eq!(aggregate_backends.len(), 16);
    assert!(aggregate_backends.iter().all(|backend| matches!(
        backend,
        TorusMacBackend::Wgpu {
            algorithm: TorusWgpuAlgorithm::ExactTransformResidentPbs,
            ..
        }
    )));
    let aggregate_oracle_clear: bool = aggregate_oracle.decrypt(&client);
    let aggregate_gpu_clear: u32 = aggregate_gpu.decrypt(&client);
    assert_eq!(aggregate_gpu_clear, u32::from(aggregate_oracle_clear));
    assert_eq!(aggregate_gpu_clear, 1);
    eprintln!(
        "high-level scalar-gt: encrypted aggregate 32768+32768 > 65535 result=1 16-block-WGPU={:.3}ms",
        aggregate_time.as_secs_f64() * 1_000.0,
    );

    // The result is an ordinary high-level ciphertext, not a private adapter
    // object: it can immediately govern a normal encrypted branch.
    let predicate = true_predicate.expect("the clear > clear-1 case must be true");
    let encrypted_condition = predicate.gt(0u32);
    let chosen = encrypted_condition.if_then_else(
        &FheUint32::encrypt(0xcafe_babeu32, &client),
        &FheUint32::encrypt(0xdead_beefu32, &client),
    );
    let chosen_clear: u32 = chosen.decrypt(&client);
    assert_eq!(chosen_clear, 0xcafe_babe);

    // Carry state is semantic input to a radix comparison. The narrow WGPU
    // machine intentionally refuses dirty blocks instead of silently treating
    // their unpropagated carry as an independent base-4 digit.
    let dirty = FheUint32::encrypt(7u32, &client);
    let (mut dirty_radix, dirty_id, dirty_tag, dirty_rerandomization) = dirty.into_raw_parts();
    dirty_radix.blocks_mut()[0].degree = tfhe::shortint::ciphertext::Degree::new(4);
    let dirty = FheUint32::from_raw_parts(dirty_radix, dirty_id, dirty_tag, dirty_rerandomization);
    assert!(matches!(
        plan.greater_than_scalar(&dirty, 6),
        Err(FheUint32WgpuPbsError::NonEmptyCarries)
    ));

    eprintln!(
        "high-level scalar-gt: prepare={:.3}ms total-three-comparisons={:.3}ms",
        prepare_time.as_secs_f64() * 1_000.0,
        gpu_times.iter().sum::<std::time::Duration>().as_secs_f64() * 1_000.0,
    );
}

#[test]
fn deployed_fhe_uint32_scalar_gt_resident_matches_roundtrip_baseline() {
    if std::env::var_os("DREGG_REQUIRE_WGPU").is_none() {
        eprintln!("set DREGG_REQUIRE_WGPU=1 to run the resident scalar comparison GPU gate");
        return;
    }

    let client = ClientKey::generate(ConfigBuilder::default());
    let compressed = CompressedServerKey::new(&client);
    let server = compressed.decompress();
    let plan = prepare_fhe_uint32_ks_pbs_transform_wgpu_plan(&compressed).unwrap();
    set_server_key(server);

    let clear = 0x9234_5678u32;
    let scalar = clear - 1;
    let input = FheUint32::encrypt(clear, &client);
    let oracle = input.gt(scalar);

    let roundtrip_started = Instant::now();
    let (roundtrip, roundtrip_backends) = plan.greater_than_scalar(&input, scalar).unwrap();
    let roundtrip_time = roundtrip_started.elapsed();
    assert_eq!(roundtrip_backends.len(), 16);

    let resident_started = Instant::now();
    let (resident, resident_backend) = plan.greater_than_scalar_resident(&input, scalar).unwrap();
    let resident_time = resident_started.elapsed();
    assert!(matches!(
        resident_backend,
        TorusMacBackend::Wgpu {
            algorithm: TorusWgpuAlgorithm::ExactTransformResidentPbs,
            ..
        }
    ));
    let oracle_clear: bool = oracle.decrypt(&client);
    let roundtrip_clear: u32 = roundtrip.decrypt(&client);
    let resident_clear: u32 = resident.decrypt(&client);
    assert_eq!(roundtrip_clear, u32::from(oracle_clear));
    assert_eq!(resident_clear, roundtrip_clear);
    eprintln!(
        "high-level scalar-gt resident: roundtrip={:.3}ms resident={:.3}ms speedup={:.3}x",
        roundtrip_time.as_secs_f64() * 1_000.0,
        resident_time.as_secs_f64() * 1_000.0,
        roundtrip_time.as_secs_f64() / resident_time.as_secs_f64(),
    );

    // Cover the other lexicographic paths independently: complete equality,
    // a more-significant less decision, and a more-significant greater
    // decision. The timed case above is the late (least-significant) greater
    // decision, so together these exercise state retention across the chain.
    for scalar in [clear, 0xa234_5678, 0x8234_5678] {
        let oracle = input.gt(scalar);
        let (resident_case, backend) = plan.greater_than_scalar_resident(&input, scalar).unwrap();
        assert!(matches!(
            backend,
            TorusMacBackend::Wgpu {
                algorithm: TorusWgpuAlgorithm::ExactTransformResidentPbs,
                ..
            }
        ));
        let oracle_clear: bool = oracle.decrypt(&client);
        let resident_clear: u32 = resident_case.decrypt(&client);
        assert_eq!(resident_clear, u32::from(oracle_clear));
    }

    // The resident result is still an ordinary high-level ciphertext and can
    // immediately govern encrypted control flow.
    let condition = resident.gt(0u32);
    let chosen = condition.if_then_else(
        &FheUint32::encrypt(0xcafe_babeu32, &client),
        &FheUint32::encrypt(0xdead_beefu32, &client),
    );
    let chosen_clear: u32 = chosen.decrypt(&client);
    assert_eq!(chosen_clear, 0xcafe_babe);

    // Dark-Bazaar-shaped producer: compare a computed encrypted aggregate,
    // including a transition across the old u16 boundary, without any
    // intermediate host ciphertext round trip.
    let encrypted_quantities = [
        FheUint32::encrypt(32_768u32, &client),
        FheUint32::encrypt(32_768u32, &client),
    ];
    let quantity_refs = encrypted_quantities.iter().collect::<Vec<_>>();
    let aggregate = FheUint32::sum(&quantity_refs);
    let aggregate_oracle = aggregate.gt(65_535u32);
    let (aggregate_resident, aggregate_backend) = plan
        .greater_than_scalar_resident(&aggregate, 65_535)
        .unwrap();
    assert!(matches!(
        aggregate_backend,
        TorusMacBackend::Wgpu {
            algorithm: TorusWgpuAlgorithm::ExactTransformResidentPbs,
            ..
        }
    ));
    let aggregate_clear: u32 = aggregate_resident.decrypt(&client);
    let aggregate_oracle_clear: bool = aggregate_oracle.decrypt(&client);
    assert_eq!(aggregate_clear, u32::from(aggregate_oracle_clear));
    assert_eq!(aggregate_clear, 1);

    let dirty = FheUint32::encrypt(7u32, &client);
    let (mut dirty_radix, dirty_id, dirty_tag, dirty_rerandomization) = dirty.into_raw_parts();
    dirty_radix.blocks_mut()[0].degree = tfhe::shortint::ciphertext::Degree::new(4);
    let dirty = FheUint32::from_raw_parts(dirty_radix, dirty_id, dirty_tag, dirty_rerandomization);
    assert!(matches!(
        plan.greater_than_scalar_resident(&dirty, 6),
        Err(FheUint32WgpuPbsError::NonEmptyCarries)
    ));
}

#[test]
fn deployed_fhe_uint32_ciphertext_gt_resident_matches_tfhe_and_selects_privately() {
    if std::env::var_os("DREGG_REQUIRE_WGPU").is_none() {
        eprintln!("set DREGG_REQUIRE_WGPU=1 to run the resident ciphertext comparison GPU gate");
        return;
    }

    let client = ClientKey::generate(ConfigBuilder::default());
    let compressed = CompressedServerKey::new(&client);
    let server = compressed.decompress();
    let plan = prepare_fhe_uint32_ks_pbs_transform_wgpu_plan(&compressed).unwrap();
    set_server_key(server);

    // Equality, a least-significant greater decision, and both directions of
    // an early most-significant decision cover the complete lexicographic
    // state machine. The oracle is tfhe-rs's independent ciphertext-to-
    // ciphertext comparison; neither operand nor predicate is decrypted until
    // both encrypted computations finish.
    let cases = [
        (0x9234_5678u32, 0x9234_5678u32),
        (0x9234_5678u32, 0x9234_5677u32),
        (0x9234_5678u32, 0xa234_5678u32),
        (0xa234_5678u32, 0x9234_5678u32),
    ];
    let mut resident_times = Vec::with_capacity(cases.len());
    for (lhs_clear, rhs_clear) in cases {
        let lhs = FheUint32::encrypt(lhs_clear, &client);
        let rhs = FheUint32::encrypt(rhs_clear, &client);
        let oracle = lhs.gt(&rhs);
        let started = Instant::now();
        let (resident, backend) = plan.greater_than_ciphertext_resident(&lhs, &rhs).unwrap();
        let elapsed = started.elapsed();
        resident_times.push(elapsed);
        assert!(matches!(
            backend,
            TorusMacBackend::Wgpu {
                algorithm: TorusWgpuAlgorithm::ExactTransformResidentPbs,
                ..
            }
        ));
        let oracle_clear: bool = oracle.decrypt(&client);
        let resident_clear: u32 = resident.decrypt(&client);
        assert_eq!(resident_clear, u32::from(oracle_clear));
        eprintln!(
            "high-level ciphertext-gt resident: lhs={lhs_clear:#010x} rhs={rhs_clear:#010x} result={resident_clear} 31-PBS-WGPU={:.3}ms",
            elapsed.as_secs_f64() * 1_000.0,
        );
    }

    // Bazaar-shaped private winner selection. Comparison and all 16 selected
    // lot blocks execute as one resident WGPU program: no predicate ciphertext
    // is returned to the host or converted through tfhe-rs's CPU CMUX path.
    // The independent oracle is tfhe-rs comparison + `if_then_else` and covers
    // true, false, and equal (false-branch) decisions.
    let select_cases = [
        (91_000u32, 87_500u32),
        (82_000u32, 93_000u32),
        (77_777u32, 77_777u32),
    ];
    let mut select_times = Vec::with_capacity(select_cases.len());
    for (left_clear, right_clear) in select_cases {
        let left_bid = FheUint32::encrypt(left_clear, &client);
        let right_bid = FheUint32::encrypt(right_clear, &client);
        let left_lot = FheUint32::encrypt(0x1111_1111u32, &client);
        let right_lot = FheUint32::encrypt(0x2222_2222u32, &client);
        let oracle_condition = left_bid.gt(&right_bid);
        let oracle_lot = oracle_condition.if_then_else(&left_lot, &right_lot);
        let select_started = Instant::now();
        let (selected_lot, select_backend) = plan
            .select_by_greater_than_resident(&left_bid, &right_bid, &left_lot, &right_lot)
            .unwrap();
        let select_time = select_started.elapsed();
        select_times.push(select_time);
        assert!(matches!(
            select_backend,
            TorusMacBackend::Wgpu {
                algorithm: TorusWgpuAlgorithm::ExactTransformResidentPbs,
                ..
            }
        ));
        let selected_lot_clear: u32 = selected_lot.decrypt(&client);
        let oracle_lot_clear: u32 = oracle_lot.decrypt(&client);
        assert_eq!(selected_lot_clear, oracle_lot_clear);

        // Metadata/noise reconstruction is production-shaped: the selected
        // result survives a subsequent ordinary high-level operation.
        let incremented = &selected_lot + FheUint32::encrypt(1u32, &client);
        let incremented_clear: u32 = incremented.decrypt(&client);
        assert_eq!(incremented_clear, selected_lot_clear.wrapping_add(1));
        eprintln!(
            "high-level fused ciphertext-gt/select: lhs={left_clear} rhs={right_clear} selected={selected_lot_clear:#010x} 63-PBS-WGPU={:.3}ms",
            select_time.as_secs_f64() * 1_000.0,
        );
    }

    let clean = FheUint32::encrypt(7u32, &client);
    let dirty = FheUint32::encrypt(6u32, &client);
    let (mut dirty_radix, dirty_id, dirty_tag, dirty_rerandomization) = dirty.into_raw_parts();
    dirty_radix.blocks_mut()[0].degree = tfhe::shortint::ciphertext::Degree::new(4);
    let dirty = FheUint32::from_raw_parts(dirty_radix, dirty_id, dirty_tag, dirty_rerandomization);
    assert!(matches!(
        plan.greater_than_ciphertext_resident(&clean, &dirty),
        Err(FheUint32WgpuPbsError::NonEmptyCarries)
    ));
    let clean_lot = FheUint32::encrypt(11u32, &client);
    assert!(matches!(
        plan.select_by_greater_than_resident(&clean, &clean, &dirty, &clean_lot),
        Err(FheUint32WgpuPbsError::NonEmptyCarries)
    ));

    eprintln!(
        "high-level ciphertext-gt resident: four-comparison-total={:.3}ms encrypted-select={:.3}ms",
        resident_times
            .iter()
            .sum::<std::time::Duration>()
            .as_secs_f64()
            * 1_000.0,
        select_times
            .iter()
            .sum::<std::time::Duration>()
            .as_secs_f64()
            * 1_000.0,
    );
}
