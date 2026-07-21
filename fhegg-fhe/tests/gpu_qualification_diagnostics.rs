use fhegg_fhe::bfv_lean::{fold, LeanCiphertext, RnsPoly, FOLD_MODULI};
use fhegg_fhe::gpu_arena::{FoldBackend, FoldCapacity, ResidentFoldPlan};
use fhegg_fhe::gpu_qualification::{
    diagnose_fold_backend, AdapterUnavailableReason, BfvFoldDispatch, BfvFoldPolicy,
    CpuFallbackReason, DiagnosedFoldEngine, FoldCapacityReport, ResidentFoldPlanReport,
    WgpuAdapterProfile, WgpuAdapterStatus, WgpuFoldLimits,
};

fn ciphertext(moduli: Vec<u64>) -> LeanCiphertext {
    let degree = 8;
    let polys = (0..2)
        .map(|poly| RnsPoly {
            rows: moduli
                .iter()
                .enumerate()
                .map(|(row, &modulus)| {
                    (0..degree)
                        .map(|column| {
                            u64::try_from(poly + row + column + 1)
                                .expect("tiny test coefficient index fits u64")
                                % modulus
                        })
                        .collect()
                })
                .collect(),
        })
        .collect();
    LeanCiphertext {
        moduli,
        degree,
        level: 0,
        variable_time: false,
        polys,
        plain_bound: 1,
    }
}

fn adapter() -> WgpuAdapterStatus {
    WgpuAdapterStatus::Available {
        adapter: WgpuAdapterProfile {
            name: "test-adapter".to_owned(),
            backend: "Vulkan".to_owned(),
            device_type: "DiscreteGpu".to_owned(),
            vendor_id: 0x1002,
            device_id: 0x73df,
            driver: "test-driver".to_owned(),
            driver_info: "test-info".to_owned(),
            limits: WgpuFoldLimits {
                max_buffer_size: 1 << 30,
                max_storage_buffer_binding_size: 1 << 29,
                effective_storage_bytes: 1 << 29,
                max_compute_workgroups_per_dimension: 65_535,
                max_compute_invocations_per_workgroup: 256,
                max_compute_workgroup_size_x: 256,
            },
        },
    }
}

#[test]
fn explicit_cpu_policy_is_named_and_bit_exact() {
    let ciphertexts = vec![
        ciphertext(FOLD_MODULI.to_vec()),
        ciphertext(FOLD_MODULI.to_vec()),
    ];
    let expected = fold(&ciphertexts, 1 << 20).expect("CPU oracle");
    let engine = DiagnosedFoldEngine::cpu_only();
    let execution = engine
        .fold(&ciphertexts, 1 << 20)
        .expect("diagnosed CPU fold");
    assert_eq!(execution.ciphertext, expected);
    assert_eq!(
        execution.dispatch,
        BfvFoldDispatch::CpuFallback {
            reason: CpuFallbackReason::PolicyForcedCpu,
        }
    );
}

#[test]
fn every_cpu_fallback_class_has_a_specific_diagnostic() {
    let no_adapter = WgpuAdapterStatus::Unavailable {
        reason: AdapterUnavailableReason::NoHighPerformanceAdapter,
    };
    assert_eq!(
        diagnose_fold_backend(
            BfvFoldPolicy::Auto,
            &no_adapter,
            &FOLD_MODULI,
            FoldBackend::CpuNoArena,
            None,
        ),
        BfvFoldDispatch::CpuFallback {
            reason: CpuFallbackReason::NoHighPerformanceAdapter,
        }
    );

    assert_eq!(
        diagnose_fold_backend(
            BfvFoldPolicy::Auto,
            &adapter(),
            &FOLD_MODULI,
            FoldBackend::CpuNoArena,
            None,
        ),
        BfvFoldDispatch::CpuFallback {
            reason: CpuFallbackReason::ArenaDeviceRequestFailed {
                adapter_name: "test-adapter".to_owned(),
                backend: "Vulkan".to_owned(),
            },
        }
    );

    let wrong_moduli = vec![17, 19, 23];
    assert_eq!(
        diagnose_fold_backend(
            BfvFoldPolicy::Auto,
            &adapter(),
            &wrong_moduli,
            FoldBackend::CpuUnsupportedShape,
            None,
        ),
        BfvFoldDispatch::CpuFallback {
            reason: CpuFallbackReason::UnsupportedRnsModulusSet {
                expected: FOLD_MODULI.to_vec(),
                actual: wrong_moduli,
            },
        }
    );
}

#[test]
fn resident_dispatch_carries_the_exact_capacity_and_plan() {
    let plan = ResidentFoldPlan {
        input_ciphertexts: 17,
        ciphertexts_per_chunk: 8,
        upload_chunks: 3,
        reduction_rounds: 1,
    };
    let capacity = FoldCapacity {
        max_storage_bytes: 1 << 30,
        ciphertext_bytes: 196_608,
        ciphertexts_per_chunk: 5_461,
    };
    let dispatch = diagnose_fold_backend(
        BfvFoldPolicy::Auto,
        &adapter(),
        &FOLD_MODULI,
        FoldBackend::GpuResident(plan),
        Some(capacity),
    );
    assert_eq!(
        dispatch,
        BfvFoldDispatch::GpuResident {
            plan: ResidentFoldPlanReport {
                input_ciphertexts: 17,
                ciphertexts_per_chunk: 8,
                upload_chunks: 3,
                reduction_rounds: 1,
            },
            capacity: FoldCapacityReport {
                max_storage_bytes: 1 << 30,
                ciphertext_bytes: 196_608,
                ciphertexts_per_chunk: 5_461,
            },
        }
    );
    let json = serde_json::to_string(&dispatch).expect("dispatch diagnostic serializes");
    assert!(json.contains("gpu_resident"));
    assert!(json.contains("ciphertexts_per_chunk"));
}
