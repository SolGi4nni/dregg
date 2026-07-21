//! Auditable qualification and dispatch diagnostics for the existing BFV
//! additive-fold GPU path.
//!
//! The accelerator in this crate is portable [`wgpu`] compute. On `hbox` that
//! means Vulkan on the AMD RX 6750 XT; this module does not require or imply a
//! CUDA, HIP, or ROCm backend. The goal is narrower and operationally useful:
//!
//! - expose the exact adapter selected by wgpu and the buffer/dispatch limits
//!   that bound [`crate::gpu_arena::FoldEngine`];
//! - attach a named reason to every CPU fallback instead of asking an operator
//!   to infer it from `CpuNoArena`;
//! - keep actual execution authoritative. A visible adapter is not reported as
//!   a successful GPU dispatch unless `FoldEngine` really returned
//!   [`FoldBackend::GpuResident`].
//!
//! This is diagnostics, not an automatic performance policy. The crossover is
//! host-, driver-, shape-, and workload-dependent; `gpu_fold_qualify` measures
//! it rather than baking a threshold learned on one machine into consensus or
//! proof code.

use serde::Serialize;

use crate::bfv_lean::{BfvLeanError, LeanCiphertext, FOLD_MODULI};
use crate::gpu_arena::{FoldBackend, FoldCapacity, FoldEngine, ResidentFoldPlan};

/// Serializable adapter limits relevant to the BFV resident fold.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct WgpuFoldLimits {
    pub max_buffer_size: u64,
    pub max_storage_buffer_binding_size: u64,
    /// `min(max_buffer_size, max_storage_buffer_binding_size)`, exactly the
    /// ceiling used by `gpu_arena` for one resident storage binding.
    pub effective_storage_bytes: u64,
    pub max_compute_workgroups_per_dimension: u32,
    pub max_compute_invocations_per_workgroup: u32,
    pub max_compute_workgroup_size_x: u32,
}

/// The high-performance adapter selected by the same request policy as the BFV
/// arena. Strings intentionally mirror wgpu's runtime report instead of
/// pretending a particular vendor API is in use.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct WgpuAdapterProfile {
    pub name: String,
    pub backend: String,
    pub device_type: String,
    pub vendor_id: u32,
    pub device_id: u32,
    pub driver: String,
    pub driver_info: String,
    pub limits: WgpuFoldLimits,
}

/// Adapter enumeration is deliberately separate from successful device/arena
/// construction. `Available` means wgpu found this adapter, not that a kernel
/// was dispatched.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "status", rename_all = "snake_case")]
pub enum WgpuAdapterStatus {
    Available { adapter: WgpuAdapterProfile },
    Unavailable { reason: AdapterUnavailableReason },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum AdapterUnavailableReason {
    NoHighPerformanceAdapter,
}

/// Whether the caller requested runtime GPU selection or explicitly chose the
/// deterministic CPU path.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum BfvFoldPolicy {
    Auto,
    CpuOnly,
}

/// Why an execution used the CPU. These are capability/policy fallbacks, not
/// catch-all masks for malformed ciphertexts or GPU execution failures: those
/// still return [`BfvLeanError`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "reason", rename_all = "snake_case")]
pub enum CpuFallbackReason {
    PolicyForcedCpu,
    NoHighPerformanceAdapter,
    /// Adapter enumeration succeeded, but the production arena could not
    /// acquire its device. This distinction catches driver/device failures
    /// without falsely labelling the host as headless.
    ArenaDeviceRequestFailed {
        adapter_name: String,
        backend: String,
    },
    UnsupportedRnsModulusSet {
        expected: Vec<u64>,
        actual: Vec<u64>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct ResidentFoldPlanReport {
    pub input_ciphertexts: usize,
    pub ciphertexts_per_chunk: usize,
    pub upload_chunks: usize,
    pub reduction_rounds: usize,
}

impl From<ResidentFoldPlan> for ResidentFoldPlanReport {
    fn from(plan: ResidentFoldPlan) -> Self {
        Self {
            input_ciphertexts: plan.input_ciphertexts,
            ciphertexts_per_chunk: plan.ciphertexts_per_chunk,
            upload_chunks: plan.upload_chunks,
            reduction_rounds: plan.reduction_rounds,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct FoldCapacityReport {
    pub max_storage_bytes: u64,
    pub ciphertext_bytes: u64,
    pub ciphertexts_per_chunk: usize,
}

impl From<FoldCapacity> for FoldCapacityReport {
    fn from(capacity: FoldCapacity) -> Self {
        Self {
            max_storage_bytes: capacity.max_storage_bytes,
            ciphertext_bytes: capacity.ciphertext_bytes,
            ciphertexts_per_chunk: capacity.ciphertexts_per_chunk,
        }
    }
}

/// Actual backend decision for one completed fold.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "backend", rename_all = "snake_case")]
pub enum BfvFoldDispatch {
    GpuResident {
        plan: ResidentFoldPlanReport,
        capacity: FoldCapacityReport,
    },
    CpuFallback {
        reason: CpuFallbackReason,
    },
}

/// A fold output plus its evidence-bearing backend report.
#[derive(Debug, PartialEq, Eq)]
pub struct DiagnosedFoldExecution {
    pub ciphertext: LeanCiphertext,
    pub dispatch: BfvFoldDispatch,
}

/// A retained production fold engine with explicit policy and adapter
/// diagnostics. The underlying arithmetic and fallback behavior remain those
/// of [`FoldEngine`]; this wrapper only makes the decision inspectable.
pub struct DiagnosedFoldEngine {
    engine: FoldEngine,
    policy: BfvFoldPolicy,
    adapter: WgpuAdapterStatus,
}

impl DiagnosedFoldEngine {
    pub fn auto() -> Self {
        Self {
            engine: FoldEngine::new(),
            policy: BfvFoldPolicy::Auto,
            adapter: probe_high_performance_adapter(),
        }
    }

    pub fn cpu_only() -> Self {
        Self {
            engine: FoldEngine::cpu_only(),
            policy: BfvFoldPolicy::CpuOnly,
            // Enumeration is still useful in a diagnostic artifact: it shows
            // that CPU was policy-selected even if capable hardware existed.
            adapter: probe_high_performance_adapter(),
        }
    }

    pub const fn policy(&self) -> BfvFoldPolicy {
        self.policy
    }

    pub const fn adapter_status(&self) -> &WgpuAdapterStatus {
        &self.adapter
    }

    pub fn has_gpu_arena(&self) -> bool {
        self.engine.has_gpu_arena()
    }

    pub fn capacity(
        &self,
        ciphertext: &LeanCiphertext,
    ) -> Option<Result<FoldCapacityReport, BfvLeanError>> {
        self.engine
            .capacity(ciphertext)
            .map(|capacity| capacity.map(Into::into))
    }

    pub fn fold(
        &self,
        ciphertexts: &[LeanCiphertext],
        plaintext_modulus: u64,
    ) -> Result<DiagnosedFoldExecution, BfvLeanError> {
        let execution = self.engine.fold(ciphertexts, plaintext_modulus)?;
        let first = ciphertexts
            .first()
            .expect("FoldEngine rejects an empty batch before returning an execution");
        let capacity = match execution.backend {
            FoldBackend::GpuResident(_) => self.engine.capacity(first).transpose()?,
            FoldBackend::CpuNoArena | FoldBackend::CpuUnsupportedShape => None,
        };
        let dispatch = diagnose_fold_backend(
            self.policy,
            &self.adapter,
            &first.moduli,
            execution.backend,
            capacity,
        );
        Ok(DiagnosedFoldExecution {
            ciphertext: execution.ciphertext,
            dispatch,
        })
    }
}

impl Default for DiagnosedFoldEngine {
    fn default() -> Self {
        Self::auto()
    }
}

/// Classify an *actual* FoldEngine result. Kept public so diagnostics can be
/// tested without requiring a physical adapter.
pub fn diagnose_fold_backend(
    policy: BfvFoldPolicy,
    adapter: &WgpuAdapterStatus,
    rns_moduli: &[u64],
    backend: FoldBackend,
    capacity: Option<FoldCapacity>,
) -> BfvFoldDispatch {
    match backend {
        FoldBackend::GpuResident(plan) => BfvFoldDispatch::GpuResident {
            plan: plan.into(),
            capacity: capacity
                .expect("a completed resident fold must have adapter capacity")
                .into(),
        },
        FoldBackend::CpuUnsupportedShape => BfvFoldDispatch::CpuFallback {
            reason: CpuFallbackReason::UnsupportedRnsModulusSet {
                expected: FOLD_MODULI.to_vec(),
                actual: rns_moduli.to_vec(),
            },
        },
        FoldBackend::CpuNoArena if policy == BfvFoldPolicy::CpuOnly => {
            BfvFoldDispatch::CpuFallback {
                reason: CpuFallbackReason::PolicyForcedCpu,
            }
        }
        FoldBackend::CpuNoArena => match adapter {
            WgpuAdapterStatus::Unavailable { .. } => BfvFoldDispatch::CpuFallback {
                reason: CpuFallbackReason::NoHighPerformanceAdapter,
            },
            WgpuAdapterStatus::Available { adapter } => BfvFoldDispatch::CpuFallback {
                reason: CpuFallbackReason::ArenaDeviceRequestFailed {
                    adapter_name: adapter.name.clone(),
                    backend: adapter.backend.clone(),
                },
            },
        },
    }
}

/// Enumerate the adapter selected by the BFV arena's high-performance policy.
/// This does not request a device; successful dispatch remains the authority.
pub fn probe_high_performance_adapter() -> WgpuAdapterStatus {
    let instance = wgpu::Instance::default();
    let Some(adapter) =
        pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
            power_preference: wgpu::PowerPreference::HighPerformance,
            ..Default::default()
        }))
    else {
        return WgpuAdapterStatus::Unavailable {
            reason: AdapterUnavailableReason::NoHighPerformanceAdapter,
        };
    };
    let info = adapter.get_info();
    let limits = adapter.limits();
    let max_storage_buffer_binding_size = u64::from(limits.max_storage_buffer_binding_size);
    WgpuAdapterStatus::Available {
        adapter: WgpuAdapterProfile {
            name: info.name,
            backend: format!("{:?}", info.backend),
            device_type: format!("{:?}", info.device_type),
            vendor_id: info.vendor,
            device_id: info.device,
            driver: info.driver,
            driver_info: info.driver_info,
            limits: WgpuFoldLimits {
                max_buffer_size: limits.max_buffer_size,
                max_storage_buffer_binding_size,
                effective_storage_bytes: limits
                    .max_buffer_size
                    .min(max_storage_buffer_binding_size),
                max_compute_workgroups_per_dimension: limits.max_compute_workgroups_per_dimension,
                max_compute_invocations_per_workgroup: limits.max_compute_invocations_per_workgroup,
                max_compute_workgroup_size_x: limits.max_compute_workgroup_size_x,
            },
        },
    }
}
